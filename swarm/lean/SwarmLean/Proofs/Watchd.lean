import SwarmLean.Proofs
import SwarmLean.Proofs.Queue
import SwarmLean.Cmd.Watchd
import SwarmLean.Real

/-! Agents and watchd (board #106): what swarm/model proves of the lifecycle decisions (`Decide.lean`), of `swarm end`,
reap, spawn's reservation and the watchd loop, about the code that runs: `Lifecycle.fateHeard`, `fate`, `endWhy` and
`endStep`, `Watchd.keeps` and reap's steps, `Ci.prAct`, `Spawn.reserve`/`reserveTask`/`unreserve`, `Agents.bind`, and
App's `Guard`. A decision that reads the world (`Lifecycle.Reads`' monadic fields) is stated with `Sat`, a postcondition
that holds whatever each read returns. -/

namespace SwarmLean.WatchdProofs
open Agents Swarm

/-! ## `Sat`: a postcondition of a monadic run, whatever its effects return -/

/-- Every result `x` can give satisfies `p` (Batteries' `SatisfiesM`): `x` factors through results carrying a proof. -/
def Sat {m : Type → Type} [Functor m] {α : Type} (p : α → Prop) (x : m α) : Prop :=
  ∃ x' : m {a // p a}, Subtype.val <$> x' = x

section Sat
variable {m : Type → Type} [Monad m] [LawfulMonad m] {α β : Type}

theorem Sat.pure {p : α → Prop} {a : α} (h : p a) : Sat p (pure a : m α) := ⟨Pure.pure ⟨a, h⟩, by simp⟩

theorem Sat.trivial (x : m α) : Sat (fun _ => True) x := ⟨(fun a => ⟨a, True.intro⟩) <$> x, by simp⟩

theorem Sat.imp {p q : α → Prop} {x : m α} (h : Sat p x) (hq : ∀ a, p a → q a) : Sat q x := by
  obtain ⟨x', rfl⟩ := h
  exact ⟨(fun s => ⟨s.1, hq _ s.2⟩) <$> x', by simp⟩

theorem Sat.bind {p : α → Prop} {q : β → Prop} {x : m α} {f : α → m β} (hx : Sat p x) (hf : ∀ a, p a → Sat q (f a)) :
    Sat q (x >>= f) := by
  obtain ⟨x', rfl⟩ := hx
  have hf' : ∀ s : {a // p a}, ∃ y : m {b // q b}, Subtype.val <$> y = f s.1 := fun s => hf s.1 s.2
  refine ⟨x' >>= fun s => Classical.choose (hf' s), ?_⟩
  simp only [map_bind, Classical.choose_spec (hf' _), bind_map_left]

/-- A read whose answer the postcondition doesn't depend on. -/
theorem Sat.any {q : β → Prop} {x : m α} {f : α → m β} (hf : ∀ a, Sat q (f a)) : Sat q (x >>= f) :=
  Sat.bind (Sat.trivial x) fun a _ => hf a

theorem Sat.map {p : β → Prop} {x : m α} {f : α → β} (h : Sat (fun a => p (f a)) x) : Sat p (f <$> x) := by
  rw [map_eq_pure_bind]; exact Sat.bind h fun a ha => Sat.pure ha

end Sat

/-! ## Lifecycle's verdict is `Decide.fateRec` on what its reads returned (`fate_lifted`, F1's `fateRec_*`) -/

/-- The agent row's columns as `Decide.ARow` (a NULL status is no status, "" not "idle", as `Watchd.keepRow`). -/
def row (a : Agent) : Decide.ARow :=
  { ended := a.ended.map Int.toNat, status := a.status.getD "", hc := a.hc, stay := a.stay, lastActive := a.last_active,
    ctx := a.ctx_tokens.map Int.toNat, waiter := a.waiter.map Int.toNat }

/-- An hc terminal as `Decide.Term`. -/
def term (x : Option Term) : Option Decide.Term := x.map fun x => { cwd := x.cwd, status := x.status.getD "" }

/-- The Lua's verdicts as fate returns them: nil (keep), "unclean", "reuse", "end". -/
def verdictStr : Decide.Verdict → Option String
  | .keep => none | .unclean => some "unclean" | .reuse => some "reuse" | .end_ => some "end"

/-- A check's label as fate records it. -/
def label : Decide.Check → String
  | .stay => "stay" | .idle => "idle" | .terminal => "terminal" | .task => "task" | .lock => "lock"
  | .unlanded => "unlanded" | .job => "job" | .context => "context" | .waiter => "waiter"

/-- What a fate run returned is `Decide.fateRec` on facts `F`: its verdict, every check it recorded (label and value),
and the unlanded worktree and job it heard, of which `F` says only whether there was one. -/
def RecOf (a : Agent) (t : Int) (x : Option Term) (hasTerms : Bool) (all : Bool) (F : Decide.Facts)
    (r : Option String × Lifecycle.Heard) : Prop :=
  r.2.held.isSome = F.unlanded ∧ r.2.proc.isSome = F.job ∧
    r.1 = verdictStr (Decide.fateRec (row a) t (term x) hasTerms F all).1 ∧
    r.2.checks = (Decide.fateRec (row a) t (term x) hasTerms F all).2.map fun p => (label p.1, p.2)

/-- `F`'s pure parts are the reads' pure fields. -/
def Agrees {m : Type → Type} (f : Lifecycle.Reads m) (F : Decide.Facts) : Prop :=
  F.claims = f.claims ∧ F.locks = f.locks ∧ F.pool = f.pool ∧ F.passedOver = f.passedOver

theorem py_isSome (o : Option String) : (py o).isSome = Decide.nz o := by
  cases o with
  | none => rfl
  | some s => by_cases h : s = "" <;> simp [py, Decide.nz, Option.filter, h]

theorem ctx_small (o : Option Int) : (decide ((o.map Int.toNat).getD 0 < Decide.smallCtx)) = decide (o.getD 0 < SMALL_CTX) := by
  cases o with
  | none => rfl
  | some i => show decide (i.toNat < 40000) = decide (i < 40000); rw [decide_eq_decide]; omega

/-- The facts of one fate run: the reads' pure fields and the answers `o` (ours), `u` (unlanded), `j` (job), `w` (alive). -/
def mkF {m : Type → Type} (f : Lifecycle.Reads m) (o : Bool) (u : Option (String × List String))
    (j : Option Machine.Ps) (w : Bool) : Decide.Facts :=
  { ours := o, claims := f.claims, locks := f.locks, unlanded := u.isSome, job := j.isSome, pool := f.pool,
    passedOver := f.passedOver, alive := w }

theorem bne_dec {α : Type} [DecidableEq α] [BEq α] [LawfulBEq α] (a b : α) : (a != b) = !decide (a = b) := by
  by_cases h : a = b <;> simp [h]

theorem ite_sat {m : Type → Type} [Monad m] {α : Type} {p : α → Prop} {c : Prop} [Decidable c] {x y : m α}
    (h1 : c → Sat p x) (h2 : ¬c → Sat p y) : Sat p (if c then x else y) := by
  by_cases h : c
  · rw [ite_eq_left h]; exact h1 h
  · rw [ite_eq_right h]; exact h2 h

/-- fate's busy terminal: bound, hc answered, and its terminal not idle or done (or not listed). -/
def busyL (a : Agent) (hasTerms : Bool) (x : Option Term) : Bool :=
  (py a.hc).isSome && hasTerms && match x with
    | none => true
    | some x => x.status != some "idle" && x.status != some "done"

section Vals
variable (a : Agent) (t : Int) (x : Option Term) (hasTerms : Bool) (F : Decide.Facts)

theorem v_stay : Decide.Check.val (row a) t (term x) hasTerms F .stay = (py a.stay).isSome := (py_isSome _).symm

theorem v_idle : Decide.Check.val (row a) t (term x) hasTerms F .idle =
    (a.status != some "idle" || decide (t - a.last_active.getD 0 < 120)) := by
  show (a.status.getD "" != "idle" || decide (t - a.last_active.getD 0 < 120)) = _
  cases a.status with
  | none => simp
  | some v => simp only [Option.getD_some, bne_dec, Option.some.injEq]

theorem busy_eq : (Decide.nz (row a).hc && hasTerms && (term x).all fun x => x.status != "idle" && x.status != "done") =
    busyL a hasTerms x := by
  rw [show (row a).hc = a.hc from rfl, ← py_isSome]
  unfold busyL
  cases x with
  | none => rfl
  | some y =>
    simp only [term, Option.map_some, Option.all_some]
    cases y.status with
    | none => simp
    | some v => simp only [Option.getD_some, bne_dec, Option.some.injEq]

theorem v_terminal_none (h : ((x.bind fun x => x.cwd).bind fun x => py (some x)) = none) :
    Decide.Check.val (row a) t (term x) hasTerms F .terminal =
    (busyL a hasTerms x) := by
  simp only [Decide.Check.val]
  rw [busy_eq]
  have : (term x).any (fun x => Decide.nz x.cwd && !F.ours) = false := by
    cases x with
    | none => rfl
    | some y =>
      simp only [Option.bind_some] at h
      simp only [term, Option.map_some, Option.any_some]
      cases hc : y.cwd with
      | none => rfl
      | some c => rw [hc] at h; simp only [Option.bind_some] at h; have := py_isSome (some c); rw [h] at this
                  simp [← this]
  rw [this, Bool.false_or]

theorem v_terminal_some {c : String} (h : ((x.bind fun x => x.cwd).bind fun x => py (some x)) = some c) :
    Decide.Check.val (row a) t (term x) hasTerms F .terminal =
    (!F.ours || busyL a hasTerms x) := by
  simp only [Decide.Check.val]
  rw [busy_eq]
  have : (term x).any (fun x => Decide.nz x.cwd && !F.ours) = !F.ours := by
    cases x with
    | none => simp at h
    | some y =>
      simp only [Option.bind_some] at h
      simp only [term, Option.map_some, Option.any_some]
      cases hc : y.cwd with
      | none => rw [hc] at h; simp at h
      | some c' => rw [hc] at h; simp only [Option.bind_some] at h; have := py_isSome (some c'); rw [h] at this
                   simp [← this]
  rw [this]

theorem v_context : Decide.Check.val (row a) t (term x) hasTerms F .context =
    (decide (a.ctx_tokens.getD 0 < SMALL_CTX) && decide (F.pool > 0) && !F.passedOver) := by
  show (decide ((a.ctx_tokens.map Int.toNat).getD 0 < Decide.smallCtx) && decide (F.pool > 0) && !F.passedOver) = _
  rw [ctx_small]

theorem v_waiter : Decide.Check.val (row a) t (term x) hasTerms F .waiter = (a.waiter.isSome && F.alive) := by
  simp only [Decide.Check.val, row, Option.isSome_map]

theorem v_task : Decide.Check.val (row a) t (term x) hasTerms F .task = F.claims := rfl
theorem v_lock : Decide.Check.val (row a) t (term x) hasTerms F .lock = F.locks := rfl
theorem v_unlanded : Decide.Check.val (row a) t (term x) hasTerms F .unlanded = F.unlanded := rfl
theorem v_job : Decide.Check.val (row a) t (term x) hasTerms F .job = F.job := rfl

end Vals

/-! `Decide.fateRecV` by the first check that holds. -/

section Fr
open Decide
variable {V : Check → Bool} {all : Bool}

theorem fr_stay (h : (V .stay && !all) = true) : fateRecV V all = (.keep, [(.stay, true)]) := by
  simp [fateRecV, orRec, h]

theorem fr_idle (h1 : (V .stay && !all) = false) (h : (V .idle && !all) = true) :
    fateRecV V all = (.keep, [(.stay, V .stay), (.idle, true)]) := by
  simp [fateRecV, orRec, h1, h]

theorem fr_terminal (h1 : (V .stay && !all) = false) (h2 : (V .idle && !all) = false)
    (h : (V .terminal && !all) = true) :
    fateRecV V all = (.keep, [(.stay, V .stay), (.idle, V .idle), (.terminal, true)]) := by
  simp [fateRecV, orRec, h1, h2, h]

theorem fr_task (h1 : (V .stay && !all) = false) (h2 : (V .idle && !all) = false)
    (h3 : (V .terminal && !all) = false) (h : (V .task && !all) = true) :
    fateRecV V all = (.keep, [(.stay, V .stay), (.idle, V .idle), (.terminal, V .terminal), (.task, true)]) := by
  simp [fateRecV, orRec, h1, h2, h3, h]

theorem fr_lock (h1 : (V .stay && !all) = false) (h2 : (V .idle && !all) = false)
    (h3 : (V .terminal && !all) = false) (h4 : (V .task && !all) = false) (h : (V .lock && !all) = true) :
    fateRecV V all = (.keep, [(.stay, V .stay), (.idle, V .idle), (.terminal, V .terminal), (.task, V .task),
      (.lock, true)]) := by
  simp [fateRecV, orRec, h1, h2, h3, h4, h]

/-- The five checks before the unlanded one, none holding. -/
def five (V : Check → Bool) : List (Check × Bool) :=
  [(.stay, V .stay), (.idle, V .idle), (.terminal, V .terminal), (.task, V .task), (.lock, V .lock)]

theorem fr_unlanded (h1 : (V .stay && !all) = false) (h2 : (V .idle && !all) = false)
    (h3 : (V .terminal && !all) = false) (h4 : (V .task && !all) = false) (h5 : (V .lock && !all) = false)
    (h : (V .unlanded && !all) = true) :
    fateRecV V all = (.unclean, five V ++ [(.unlanded, V .unlanded)]) := by
  simp [fateRecV, orRec, five, h1, h2, h3, h4, h5, h]

theorem fr_job (h1 : (V .stay && !all) = false) (h2 : (V .idle && !all) = false)
    (h3 : (V .terminal && !all) = false) (h4 : (V .task && !all) = false) (h5 : (V .lock && !all) = false)
    (h6 : (V .unlanded && !all) = false) (h : (V .job && !all) = true) :
    fateRecV V all = (.keep, five V ++ [(.unlanded, V .unlanded)] ++ [(.job, V .job)]) := by
  simp [fateRecV, orRec, five, h1, h2, h3, h4, h5, h6, h]

theorem fr_last (h1 : (V .stay && !all) = false) (h2 : (V .idle && !all) = false)
    (h3 : (V .terminal && !all) = false) (h4 : (V .task && !all) = false) (h5 : (V .lock && !all) = false)
    (h6 : (V .unlanded && !all) = false) (h7 : (V .job && !all) = false) :
    fateRecV V all = (if (V .waiter && !all) && (V .context && !all) then .reuse else .end_,
      five V ++ [(.unlanded, V .unlanded)] ++ [(.job, V .job)] ++ [(.context, V .context), (.waiter, V .waiter)]) := by
  simp only [fateRecV, orRec, five, h1, h2, h3, h4, h5, h6, h7]
  simp only [Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append]
  split <;> rfl

end Fr

/-- A check fate found false: its value rewritten to the Lean expression, then the `if`'s hypothesis. -/
macro "vneg" hv:term:max : tactic => `(tactic| first
  | (rw [v_stay]; exact Bool.eq_false_iff.mpr ‹_›) | (rw [v_idle]; exact Bool.eq_false_iff.mpr ‹_›)
  | (rw [$hv:term]; exact Bool.eq_false_iff.mpr ‹_›) | exact Bool.eq_false_iff.mpr ‹_›)

/-- The check fate stopped at. -/
macro "vpos" hv:term:max : tactic => `(tactic| first
  | (rw [v_stay]; exact ‹_›) | (rw [v_idle]; exact ‹_›) | (rw [$hv:term]; exact ‹_›) | exact ‹_›)

/-- One leaf of fate's run: the result is `pure`, its facts `mkF f o u j w`, the verdict by lemma `fr`. -/
macro "leaf" fr:ident o:term:max u:term:max j:term:max w:term:max hv:term:max : tactic => `(tactic|
  exact Sat.pure ⟨mkF _ $o $u $j $w, ⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, by
    rw [Decide.fateRec, $fr:ident] <;> first | vneg $hv | vpos $hv | skip
    all_goals try simp only [v_context, v_waiter, mkF]
    all_goals first | rfl | (simp_all [verdictStr, busyL] <;> rfl) | (simp_all [verdictStr, busyL] <;> split <;> rfl), by
    rw [Decide.fateRec, $fr:ident] <;> first | vneg $hv | vpos $hv | skip
    all_goals simp only [five, List.map, label, List.nil_append, List.cons_append, List.singleton_append,
      v_stay, v_idle, v_task, v_lock, v_unlanded, v_job, v_context, v_waiter, $hv:term, mkF, busyL]
    all_goals first | rfl | (simp_all <;> rfl)⟩)

set_option maxHeartbeats 1000000 in
/-- Lifecycle's run on agent row `a` is `Decide.fateRec` (so its verdict, without `all`, `Decide.fateL`) on what its
reads returned, for any monad and any reads: `F` is the reads' pure fields and the answers of `ours`, `unlanded`, `job`
and `alive`. -/
theorem fateHeard_rec {m : Type → Type} [Monad m] [LawfulMonad m] (a : Agent) (t : Int) (x : Option Term)
    (hasTerms : Bool) (f : Lifecycle.Reads m) (all : Bool) :
    Sat (fun r => ∃ F, Agrees f F ∧ RecOf a t x hasTerms all F r) (Lifecycle.fateHeard a t x hasTerms f all) := by
  unfold Lifecycle.fateHeard
  simp only [pure_bind]
  refine ite_sat (fun _ => ?_) (fun _ => ?_)
  · leaf fr_stay true none none false True.intro
  refine ite_sat (fun _ => ?_) (fun _ => ?_)
  · leaf fr_idle true none none false True.intro
  cases hc : (x.bind fun x => x.cwd).bind fun x => py (some x) with
  | none =>
    dsimp only
    refine ite_sat (fun _ => ?_) (fun _ => ?_)
    · leaf fr_terminal true none none false (v_terminal_none a t x hasTerms (h := hc))
    refine ite_sat (fun _ => ?_) (fun _ => ?_)
    · leaf fr_task true none none false (v_terminal_none a t x hasTerms (h := hc))
    refine ite_sat (fun _ => ?_) (fun _ => ?_)
    · leaf fr_lock true none none false (v_terminal_none a t x hasTerms (h := hc))
    refine Sat.any fun u => ?_
    refine ite_sat (fun _ => ?_) (fun _ => ?_)
    · leaf fr_unlanded true u none false (v_terminal_none a t x hasTerms (h := hc))
    refine Sat.any fun j => ?_
    refine ite_sat (fun _ => ?_) (fun _ => ?_)
    · leaf fr_job true u j false (v_terminal_none a t x hasTerms (h := hc))
    cases hw : a.waiter with
    | none => simp only; leaf fr_last true u j false (v_terminal_none a t x hasTerms (h := hc))
    | some p => simp only; refine Sat.any fun w => ?_; leaf fr_last true u j w (v_terminal_none a t x hasTerms (h := hc))
  | some c =>
    simp only
    refine Sat.any fun o => ?_
    refine ite_sat (fun _ => ?_) (fun _ => ?_)
    · leaf fr_terminal o none none false (v_terminal_some a t x hasTerms (h := hc))
    refine ite_sat (fun _ => ?_) (fun _ => ?_)
    · leaf fr_task o none none false (v_terminal_some a t x hasTerms (h := hc))
    refine ite_sat (fun _ => ?_) (fun _ => ?_)
    · leaf fr_lock o none none false (v_terminal_some a t x hasTerms (h := hc))
    refine Sat.any fun u => ?_
    refine ite_sat (fun _ => ?_) (fun _ => ?_)
    · leaf fr_unlanded o u none false (v_terminal_some a t x hasTerms (h := hc))
    refine Sat.any fun j => ?_
    refine ite_sat (fun _ => ?_) (fun _ => ?_)
    · leaf fr_job o u j false (v_terminal_some a t x hasTerms (h := hc))
    cases hw : a.waiter with
    | none => simp only; leaf fr_last o u j false (v_terminal_some a t x hasTerms (h := hc))
    | some p => simp only; refine Sat.any fun w => ?_; leaf fr_last o u j w (v_terminal_some a t x hasTerms (h := hc))

theorem verdictStr_end {v : Decide.Verdict} (h : verdictStr v = some "end" ∨ verdictStr v = some "reuse") :
    v = .end_ ∨ v = .reuse := by
  cases v <;> simp_all [verdictStr]

/-- `Decide.fate_lifted` on the code: lifecycle's verdict on `a` is `Decide.fateL` on the facts its reads returned. -/
theorem fate_lifted {m : Type → Type} [Monad m] [LawfulMonad m] (a : Agent) (t : Int) (x : Option Term)
    (hasTerms : Bool) (f : Lifecycle.Reads m) :
    Sat (fun v => ∃ F, Agrees f F ∧ v = verdictStr (Decide.fateL (row a) t (term x) hasTerms F))
      (Lifecycle.fate a t x hasTerms f) := by
  unfold Lifecycle.fate
  refine Sat.bind (fateHeard_rec a t x hasTerms f false) fun r ⟨F, hF, hr⟩ => Sat.pure ⟨F, hF, ?_⟩
  rw [hr.2.2.1, Decide.fateRec_verdict]

/-- What a verdict to end or reuse needs, read off `Decide.fateL`: idle 2 min, staying for nothing, no claim, lock,
unlanded work or job, and not kept by its terminal. -/
theorem fateL_free {r : Decide.ARow} {t : Int} {x : Option Decide.Term} {h : Bool} {F : Decide.Facts}
    (hv : Decide.fateL r t x h F = .end_ ∨ Decide.fateL r t x h F = .reuse) :
    Decide.nz r.stay = false ∧ r.status = "idle" ∧ ¬ (t - r.lastActive.getD 0 < 120) ∧ F.claims = false ∧
      F.locks = false ∧ F.unlanded = false ∧ F.job = false := by
  simp only [Decide.fateL] at hv
  repeat' split at hv
  all_goals first | (rcases hv with hv | hv <;> cases hv) | skip
  all_goals simp_all

/-- N1 of lifecycle, and H1's `endWhy_of_fate`, on the code: a run of fate that says "end" or "reuse" found the agent
idle 2 min with no stay, no claim and no lock, and its reads returned no unlanded worktree and no job. -/
theorem fate_end_free {m : Type → Type} [Monad m] [LawfulMonad m] (a : Agent) (t : Int) (x : Option Term)
    (hasTerms : Bool) (f : Lifecycle.Reads m) :
    Sat (fun r => r.1 = some "end" ∨ r.1 = some "reuse" →
        a.status = some "idle" ∧ py a.stay = none ∧ 120 ≤ t - a.last_active.getD 0 ∧ f.claims = false ∧
          f.locks = false ∧ r.2.held = none ∧ r.2.proc = none)
      (Lifecycle.fateHeard a t x hasTerms f) := by
  refine (fateHeard_rec a t x hasTerms f false).imp fun r ⟨F, ⟨hc, hl, _, _⟩, hu, hj, hv, _⟩ he => ?_
  rw [hv, Decide.fateRec_verdict] at he
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := fateL_free (verdictStr_end he)
  refine ⟨?_, ?_, by simp only [row] at h3; omega, hc ▸ h4, hl ▸ h5, ?_, ?_⟩
  · simp only [row] at h2; cases e : a.status <;> simp_all
  · rw [show (row a).stay = a.stay from rfl, ← py_isSome] at h1; simpa using h1
  · rw [h6] at hu; simpa using hu
  · rw [h7] at hj; simpa using hj

/-- St1 on the code: lifecycle neither ends nor reuses an agent that stays for something. -/
theorem fate_keeps_stayer {m : Type → Type} [Monad m] [LawfulMonad m] (a : Agent) (t : Int) (x : Option Term)
    (hasTerms : Bool) (f : Lifecycle.Reads m) (hs : (py a.stay).isSome = true) :
    Sat (fun r => r.1 ≠ some "end" ∧ r.1 ≠ some "reuse") (Lifecycle.fateHeard a t x hasTerms f) :=
  (fate_end_free a t x hasTerms f).imp fun r h => by
    constructor <;> intro e <;> have := (h (by simp [e])).2.1 <;> simp_all

/-- F1's `fateRec_all` on the code: the agent screen's run (`all`) records every check, in fate's order, each with
its value on the facts its reads returned. -/
theorem fateHeard_all {m : Type → Type} [Monad m] [LawfulMonad m] (a : Agent) (t : Int) (x : Option Term)
    (hasTerms : Bool) (f : Lifecycle.Reads m) :
    Sat (fun r => ∃ F, Agrees f F ∧
        r.2.checks = Decide.Check.order.map fun k => (label k, k.val (row a) t (term x) hasTerms F))
      (Lifecycle.fateHeard a t x hasTerms f true) :=
  (fateHeard_rec a t x hasTerms f true).imp fun r ⟨F, hF, _, _, _, hc⟩ => ⟨F, hF, by
    rw [hc, Decide.fateRec_all, List.map_map]; rfl⟩

/-- `Decide.endWhy_lifted` on the code: `swarm end` refuses exactly when `Decide.endWhyL` does, on what its reads
returned (and its claims and locks). -/
theorem endWhy_lifted {m : Type → Type} [Monad m] [LawfulMonad m] (a : Agent) (f : Lifecycle.Reads m) :
    Sat (fun r => ∃ F : Decide.Facts, F.claims = f.claims ∧ F.locks = f.locks ∧
        r.isNone = (Decide.endWhyL (row a) F).isNone) (Lifecycle.endWhy a f) := by
  have hs : ((row a).status != "idle") = (a.status != some "idle") := by
    show (a.status.getD "" != "idle") = _
    cases a.status with
    | none => simp
    | some v => simp only [Option.getD_some, bne_dec, Option.some.injEq]
  let F (j u : Bool) : Decide.Facts := ⟨true, f.claims, f.locks, u, j, 0, false, false⟩
  unfold Lifecycle.endWhy
  refine ite_sat (fun h => Sat.pure ⟨F false false, rfl, rfl, ?_⟩) (fun h => ?_)
  · simp only [Decide.endWhyL, hs, h]; rfl
  cases hst : py a.stay with
  | some st =>
    refine Sat.pure ⟨F false false, rfl, rfl, ?_⟩
    have : Decide.nz (row a).stay = true := by rw [show (row a).stay = a.stay from rfl, ← py_isSome, hst]; rfl
    simp only [Decide.endWhyL, hs, h, this]; simp
  | none =>
    have hn : Decide.nz (row a).stay = false := by rw [show (row a).stay = a.stay from rfl, ← py_isSome, hst]; rfl
    dsimp only
    refine ite_sat (fun hc => Sat.pure ⟨F false false, rfl, rfl, ?_⟩) (fun hc => ?_)
    · simp only [Decide.endWhyL, hs, h, hn, hc, F]; simp
    refine ite_sat (fun hl => Sat.pure ⟨F false false, rfl, rfl, ?_⟩) (fun hl => ?_)
    · simp only [Decide.endWhyL, hs, h, hn, hc, hl, F]; simp
    refine Sat.any fun j => ?_
    refine ite_sat (fun hj => Sat.pure ⟨F true false, rfl, rfl, ?_⟩) (fun hj => ?_)
    · simp only [Decide.endWhyL, hs, h, hn, hc, hl, F]; simp
    refine Sat.any fun u => ?_
    cases u with
    | none => exact Sat.pure ⟨F false false, rfl, rfl, by simp_all [Decide.endWhyL, F]⟩
    | some p => exact Sat.pure ⟨F false true, rfl, rfl, by simp_all [Decide.endWhyL, F]⟩

/-- St1's `endOther_stay` on the code: `swarm end` without `--force` refuses an agent that stays for something. -/
theorem endWhy_stayer {m : Type → Type} [Monad m] [LawfulMonad m] (a : Agent) (f : Lifecycle.Reads m)
    (hs : (py a.stay).isSome = true) : Sat (fun r => r.isSome = true) (Lifecycle.endWhy a f) :=
  (endWhy_lifted a f).imp fun r ⟨F, _, _, h⟩ => by
    have hn : Decide.nz (row a).stay = true := by rw [show (row a).stay = a.stay from rfl, ← py_isSome, hs]
    have : (Decide.endWhyL (row a) F).isSome = true := by
      simp only [Decide.endWhyL, hn]; split <;> simp
    cases r <;> simp_all

/-! ## Reap's decision: `Watchd.keeps` -/

/-- `Decide.keeps_lifted` is about the code that runs: watchd's `keeps` is `Decide.keepsL` on the owner row. -/
theorem keeps_eq (o : Option Agent) (bg : Bool) (live : Option (List String)) :
    Watchd.keeps o bg live = Decide.keepsL (o.map Watchd.keepRow) bg live := rfl

/-- What keeps a lapsed claim, on the Lean row: a live owner, working, prompt-blocked or running a background job,
unless hc answered and no longer lists its bound terminal. -/
theorem keeps_iff (o : Option Agent) (bg : Bool) (live : Option (List String)) :
    Watchd.keeps o bg live = true ↔ ∃ a, o = some a ∧ a.ended = none ∧ (a.status ≠ some "idle" ∨ bg = true) ∧
      ¬ (live.isSome = true ∧ (py a.hc).isSome = true ∧ (live.getD []).contains (a.hc.getD "") = false) := by
  cases o with
  | none => simp [keeps_eq, Decide.keepsL]
  | some a =>
    have hs : (a.status.getD "" != "idle") = true ↔ a.status ≠ some "idle" := by
      cases a.status with
      | none => simp
      | some v => simp
    simp only [keeps_eq, Option.map_some, Decide.keepsL, Watchd.keepRow, Bool.and_eq_true, Bool.or_eq_true,
      Bool.not_eq_true', Option.isNone_iff_eq_none, Option.map_eq_none_iff, hs, ← py_isSome]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨a, rfl, h1, h2, by simp_all⟩
    · rintro ⟨_, ⟨⟩, h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, by simp_all⟩

/-- N1 (2), reap never reopens a claim whose live owner's job runs: such an owner keeps it, unless hc answered without
its bound terminal (then its job died with the terminal: the row is reaped as gone). -/
theorem keeps_bg {a : Agent} {live : Option (List String)} (he : a.ended = none)
    (hl : ∀ up, live = some up → (py a.hc).isSome = true → up.contains (a.hc.getD "") = true) :
    Watchd.keeps (some a) true live = true := by
  refine (keeps_iff _ _ _).2 ⟨a, rfl, he, .inr rfl, ?_⟩
  rintro ⟨h1, h2, h3⟩
  cases live with
  | none => simp at h1
  | some up => simp_all

/-! ## watchd's poll of a PR: `Ci.prAct` is `Decide.prActL` -/

/-- A PR action as the poll names it. -/
def actStr : Decide.PrAct → String
  | .done => "done" | .wake => "wake"

/-- `Decide.prAct_lifted`'s Lua side on the code: the poll's decision is `Decide.prActL` on the PR's state and verdict. -/
theorem prAct_eq (state verdict : String) (gated told : Bool) :
    Ci.prAct state verdict gated told = (Decide.prActL ⟨state, verdict⟩ gated told).map actStr := by
  simp only [Ci.prAct, Decide.prActL]
  split
  · rfl
  · split <;> rfl

/-! ## What an agent's end releases (`Agents.release`, shared by leave, end and reap) -/

theorem release_tasks (db : Db) (n : String) :
    ∀ t ∈ (release db n).tasks, t.owner = some n → t.state ≠ .claimed ∧ t.state ≠ .blocked := by
  intro t ht ho
  simp only [Agents.release, Db.setAgent, List.mem_map] at ht
  obtain ⟨u, -, rfl⟩ := ht
  split at ho
  · simp at ho
  · rename_i hc; rw [ite_eq_right hc]; simpa [ho] using hc

theorem release_locks (db : Db) (n : String) : ∀ l ∈ (release db n).locks, l.agent ≠ some n := by
  intro l hl
  simp only [Agents.release, Db.setAgent, List.mem_filter, bne_iff_ne, ne_eq] at hl
  exact hl.2

/-- A release of an agent that holds no claim and no lock leaves the tasks and locks as they were. -/
theorem release_free {db : Db} {n : String}
    (ht : ∀ t ∈ db.tasks, t.owner = some n → t.state ≠ .claimed ∧ t.state ≠ .blocked)
    (hl : ∀ l ∈ db.locks, l.agent ≠ some n) : (release db n).tasks = db.tasks ∧ (release db n).locks = db.locks := by
  refine ⟨?_, ?_⟩
  · simp only [Agents.release, Db.setAgent]
    conv => rhs; rw [← List.map_id db.tasks]
    refine List.map_congr_left fun t hm => ?_
    split
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq] at hc
      have := ht t hm hc.1; rcases hc.2 with h | h <;> simp_all
    · rfl
  · simp only [Agents.release, Db.setAgent]
    exact List.filter_eq_self.2 fun l hm => by simpa using hl l hm

theorem setAgent_tasks (db : Db) n f : (db.setAgent n f).tasks = db.tasks := rfl
theorem setAgent_locks (db : Db) n f : (db.setAgent n f).locks = db.locks := rfl
theorem log_locks (db : Db) ts a k p x : (db.log ts a k p x).locks = db.locks := rfl
theorem log_agents (db : Db) ts a k p x : (db.log ts a k p x).agents = db.agents := rfl
theorem post_locks (db : Db) n f d b u k : (Msgs.post db n f d b u k).1.locks = db.locks := rfl
theorem post_agents (db : Db) n f d b u k : (Msgs.post db n f d b u k).1.agents = db.agents := rfl

/-! ## `swarm end` and lifecycle's end: `Lifecycle.endStep` (H1, N1end) -/

/-- The agent is free in `db`: no claimed or blocked task and no lock of its. -/
def Free (db : Db) (n : String) : Prop :=
  (∀ t ∈ db.tasks, t.owner = some n → t.state ≠ .claimed ∧ t.state ≠ .blocked) ∧ ∀ l ∈ db.locks, l.agent ≠ some n

/-- N1end on the code: end_agent's transaction without `--force` ends only a live row still idle on the terminal it
was judged on, staying for nothing, and free (no claim, no lock), all as the db is when it runs. -/
theorem endStep_free {n : String} {hc by_ : Option String} {now : Int} {db : Db}
    (h : (Lifecycle.endStep n hc false by_ now db).2 = true) :
    ∃ r ∈ live db, r.name = n ∧ r.status = some "idle" ∧ r.hc = hc ∧ r.stay = none ∧ Free db n := by
  unfold Lifecycle.endStep at h
  simp only at h
  split at h
  · split at h <;> simp_all
  · rename_i r hr
    split at h
    · simp at h
    · rename_i hf
      simp only [Bool.false_or, Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true, beq_iff_eq,
        Option.isNone_iff_eq_none, List.any_eq_false] at hf
      obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hf
      have hn := List.find?_some hr
      simp only [beq_iff_eq] at hn
      refine ⟨r, List.mem_of_find?_eq_some hr, hn, h1, h2, h3, fun t ht ho => ?_, fun l hl ho => ?_⟩
      · have := h4 t ht; simp_all
      · have := h5 l hl; simp_all

/-- What an end that went through leaves: the row released and ended at `now`, with its event. -/
def ended (n : String) (force : Bool) (by_ : Option String) (now : Int) (db : Db) : Db :=
  ((Agents.release db n).setAgent n ({ · with ended := some now, status := some "ended" })).log now (some n) "end" none
    (some ((if force then "forced" else "landed") ++ (match by_ with | some b => " by " ++ b | none => "")))

theorem endStep_cases (n : String) (hc by_ : Option String) (force : Bool) (now : Int) (db : Db) :
    Lifecycle.endStep n hc force by_ now db = (db, false) ∨ Lifecycle.endStep n hc force by_ now db = (ended n force by_ now db, true) := by
  unfold Lifecycle.endStep
  simp only
  split
  · exact .inl rfl
  · split
    · exact .inl rfl
    · exact .inr rfl

/-- A refused end changes nothing. -/
theorem endStep_refused {n : String} {hc by_ : Option String} {force : Bool} {now : Int} {db : Db}
    (h : (Lifecycle.endStep n hc force by_ now db).2 = false) : (Lifecycle.endStep n hc force by_ now db).1 = db := by
  rcases endStep_cases n hc by_ force now db with e | e <;> rw [e] at h ⊢ <;> simp_all

theorem endStep_done {n : String} {hc by_ : Option String} {force : Bool} {now : Int} {db : Db}
    (h : (Lifecycle.endStep n hc force by_ now db).2 = true) :
    (Lifecycle.endStep n hc force by_ now db).1 = ended n force by_ now db := by
  rcases endStep_cases n hc by_ force now db with e | e <;> rw [e] at h ⊢ <;> simp_all

/-- `endOther_spec`'s frame on the code: an end without `--force` changes no task and no lock (the agent held none). -/
theorem endStep_frame {n : String} {hc by_ : Option String} {now : Int} {db : Db} :
    (Lifecycle.endStep n hc false by_ now db).1.tasks = db.tasks ∧
      (Lifecycle.endStep n hc false by_ now db).1.locks = db.locks := by
  cases e : (Lifecycle.endStep n hc false by_ now db).2
  · rw [endStep_refused e]; exact ⟨rfl, rfl⟩
  · obtain ⟨_, -, -, -, -, -, ht, hl⟩ := endStep_free e
    have hfree := release_free ht hl
    rw [endStep_done e]
    exact hfree

/-- An end ends the row: every row of that name is ended at `now`, and it holds no claim or lock after. -/
theorem endStep_ends {n : String} {hc by_ : Option String} {force : Bool} {now : Int} {db : Db}
    (h : (Lifecycle.endStep n hc force by_ now db).2 = true) :
    (∀ a ∈ (Lifecycle.endStep n hc force by_ now db).1.agents, a.name = n → a.ended = some now) ∧
      Free (Lifecycle.endStep n hc force by_ now db).1 n := by
  rw [endStep_done h]
  refine ⟨?_, fun t ht => release_tasks db n t ht, fun l hl => release_locks db n l hl⟩
  simp only [ended, log_agents, Db.setAgent, List.mem_map]
  rintro a ⟨b, -, rfl⟩ hb
  by_cases e : b.name = n <;> simp_all

/-! ## Reap's steps (`Watchd.reapTask`, `reapLock`, `reapGone`) -/

/-- Reap reopens only a task still claimed by the owner it judged, with its lease before `t`; that task alone changes,
to open with no owner. -/
theorem reapTask_spec {r : Task} {t now : Int} {db : Db} (h : (Watchd.reapTask r t now db).2 = true) :
    (∃ x, db.find r.id = some x ∧ x.owner = r.owner ∧ r.owner.isSome ∧ x.state = .claimed ∧
      x.lease_until.any (· < t) = true) ∧
    (Watchd.reapTask r t now db).1.tasks =
      (db.set r.id fun x => { x with state := .open, owner := none, lease_until := none }).tasks := by
  unfold Watchd.reapTask at h ⊢
  split at h
  · rename_i x hx
    simp only [hx]
    split at h
    · rename_i hc
      rw [ite_eq_left hc]
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
      exact ⟨⟨x, rfl, h1, h1 ▸ h2, h3, h4⟩, rfl⟩
    · simp at h
  · simp at h

theorem reapTask_refused {r : Task} {t now : Int} {db : Db} (h : (Watchd.reapTask r t now db).2 = false) :
    (Watchd.reapTask r t now db).1 = db := by
  unfold Watchd.reapTask at h ⊢
  split at h
  · rename_i x hx
    simp only
    split at h
    · simp at h
    · rename_i hc; rw [ite_eq_right hc]
  · simp only

/-- Reap drops only that agent's lock on the path, still expired at `t`. -/
theorem reapLock_spec {l : Lock} {t now : Int} {db : Db} (h : (Watchd.reapLock l t now db).2 = true) :
    (∃ x ∈ db.locks, x.path = l.path ∧ x.agent = l.agent ∧ x.lease_until.any (· < t) = true) ∧
    (Watchd.reapLock l t now db).1.locks = db.locks.filter fun x => !(x.path == l.path && x.agent == l.agent) := by
  unfold Watchd.reapLock at h ⊢
  split at h
  · rename_i hc
    have hc' := hc
    simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hc'
    obtain ⟨x, hx, ⟨h1, h2⟩, h3⟩ := hc'
    rw [ite_eq_left hc]
    exact ⟨⟨x, hx, h1, h2, h3⟩, rfl⟩
  · simp at h

/-- L4's step on the code: reap ends a row hc no longer lists only if it is still live and bound to that terminal;
then every row of that name is ended and it holds no claim or lock. -/
theorem reapGone_spec {n h : String} {t : Int} {db : Db} (hd : (Watchd.reapGone n h t db).2 = true) :
    (∃ x, db.agent n = some x ∧ x.hc = some h ∧ x.ended = none) ∧
    (∀ a ∈ (Watchd.reapGone n h t db).1.agents, a.name = n → a.ended = some t) ∧ Free (Watchd.reapGone n h t db).1 n := by
  unfold Watchd.reapGone at hd ⊢
  split at hd
  · rename_i hc
    simp only [hc, ↓reduceIte]
    simp only [Option.any_eq_true, Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at hc
    obtain ⟨x, hx, h1, h2⟩ := hc
    refine ⟨⟨x, hx, h1, h2⟩, ?_, fun u hu => release_tasks _ n u hu, fun l hl => release_locks _ n l hl⟩
    simp only [log_agents, Watchd.say, post_agents, Agents.release, Db.setAgent, List.mem_map]
    rintro a ⟨b, ⟨c, -, rfl⟩, rfl⟩ hb
    by_cases e : c.name = n <;> simp_all
  · simp at hd

theorem reapGone_refused {n h : String} {t : Int} {db : Db} (hd : (Watchd.reapGone n h t db).2 = false) :
    (Watchd.reapGone n h t db).1 = db := by
  unfold Watchd.reapGone at hd ⊢
  split at hd <;> simp_all

/-! ## Any order of transactions -/

/-- Every request of a replay got its answer from its step on some db. -/
theorem replay_ran {τ α : Type} (step : τ → Db → Db × α) (db : Db) (cs : List τ) :
    ∀ p ∈ (replay step db cs).2, ∃ d, (step p.1 d).2 = p.2 := by
  induction cs generalizing db with
  | nil => simp [replay]
  | cons c cs ih =>
    intro p hp
    simp only [replay, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact ⟨db, rfl⟩
    · exact ih _ p hp

/-- Under `Atomic`, every request that ran at once with others got its answer from its step on some db. -/
theorem atomic_ran {τ α : Type} {step : τ → Db → Db × α} {before after : Db} {ran : List (τ × α)}
    (h : Atomic step before after ran) : ∀ p ∈ ran, ∃ d, (step p.1 d).2 = p.2 := by
  obtain ⟨order, hp, hr⟩ := h
  intro p hm
  have : p ∈ (replay step before (order.map (·.1))).2 := by rw [hr]; exact hp.mem_iff.2 hm
  exact replay_ran step before _ p this

/-- watchd's transactions of this file, and any other transaction (`other`): what the swarm's processes run at once. -/
inductive WCmd
  | end_ (n : String) (hc : Option String) (force : Bool) (by_ : Option String) (now : Int)
  | reapTask (r : Task) (t now : Int)
  | reapLock (l : Lock) (t now : Int)
  | reapGone (n h : String) (t : Int)
  | other (f : Db → Db × Bool)

/-- Each request's step, the function the code hands `Store.txn`. -/
def WCmd.step : WCmd → Db → Db × Bool
  | .end_ n hc force by_ now => Lifecycle.endStep n hc force by_ now
  | .reapTask r t now => Watchd.reapTask r t now
  | .reapLock l t now => Watchd.reapLock l t now
  | .reapGone n h t => Watchd.reapGone n h t
  | .other f => f

/-- N1end with processes at once: an end without `--force` that answered true found, at its place in the order, the
agent live, idle on the terminal judged, staying for nothing and free, whatever else ran at the same time. -/
theorem end_atomic {before after : Db} {ran : List (WCmd × Bool)} (h : Atomic WCmd.step before after ran)
    {n : String} {hc by_ : Option String} {now : Int} (hm : (WCmd.end_ n hc false by_ now, true) ∈ ran) :
    ∃ db, ∃ r ∈ live db, r.name = n ∧ r.status = some "idle" ∧ r.hc = hc ∧ r.stay = none ∧ Free db n := by
  obtain ⟨d, hd⟩ := atomic_ran h _ hm
  exact ⟨d, endStep_free hd⟩

/-- Reap with processes at once: a reopen that answered true found the task still claimed by the owner judged, lease
lapsed; a reap of a gone row found it still live and bound to the dead terminal. -/
theorem reap_atomic {before after : Db} {ran : List (WCmd × Bool)} (h : Atomic WCmd.step before after ran) :
    (∀ r t now, (WCmd.reapTask r t now, true) ∈ ran → ∃ (db : Db) (x : Task), db.find r.id = some x ∧ x.owner = r.owner ∧
      r.owner.isSome ∧ x.state = .claimed ∧ x.lease_until.any (· < t) = true) ∧
    (∀ n hh t, (WCmd.reapGone n hh t, true) ∈ ran → ∃ (db : Db) (x : Agent), db.agent n = some x ∧ x.hc = some hh ∧ x.ended = none) := by
  refine ⟨fun r t now hm => ?_, fun n hh t hm => ?_⟩
  · obtain ⟨d, hd⟩ := atomic_ran h _ hm; exact ⟨d, (reapTask_spec hd).1⟩
  · obtain ⟨d, hd⟩ := atomic_ran h _ hm; exact ⟨d, (reapGone_spec hd).1⟩

/-! ## Spawn's reservation (auto-spawn's max, Sp1, Sp2, F1's `launch_top`) -/

/-- The user's max holds at the reservation: a reservation that went through found fewer live agents (but the
communicator) than the max, in the same transaction that adds the row. -/
theorem reserveAgent_max {db db' : Db} {e : Option String} {name cwd : String} {model : Option String} {now : Int}
    (h : Spawn.reserveAgent db e name cwd model now = .ok db') :
    ∀ x, (limits db e).2.2 = some x → ((limits db e).1 : Int) < x := by
  intro x hx
  unfold Spawn.reserveAgent at h
  split at h
  · cases h
  · generalize limits db e = L at h hx ⊢
    obtain ⟨n, mn, mx⟩ := L
    simp only at hx h ⊢
    subst hx
    simp only at h
    split at h
    · cases h
    · omega

theorem reserve_max {db : Db} {e : Option String} {name cwd : String} {model : Option String} {now : Int}
    (h : (Spawn.reserve db e name cwd model now).2 = .ok ()) :
    ∀ x, (limits db e).2.2 = some x → ((limits db e).1 : Int) < x := by
  unfold Spawn.reserve at h
  split at h
  · rename_i db' hr; exact reserveAgent_max hr
  · cases h

/-- F1's `launch_top` on the code, with the queue (board #128): auto-spawn's reservation claims task `tid` only if,
in the transaction that claims it, `tid` heads the staffing order (`Queue.staffHead`, the tasks it has not given up on)
and the max held there (a free slot). So `tid` is startable and not held, and when no startable red task is left to
staff and some startable queued task is not held, `tid` is the first such in queue order. -/
theorem reserveTask_top {db : Db} {e : Option String} {name cwd : String} {tid : Int} {model : Option String}
    {now : Int} {skip : Task → Bool} {r : Task}
    (h : (Spawn.reserveTask db e name cwd tid model now (some (Queue.staffHead skip))).2 = .ok r) :
    Queue.staffHead skip db = some tid ∧ (∀ x, (limits db e).2.2 = some x → ((limits db e).1 : Int) < x) ∧
    (∃ t ∈ Tasks.pool db, (t.id : Int) = tid ∧ t.hold = none) ∧
    ∀ q, (∀ t ∈ Queue.staffRed db, skip t = true) → (Queue.staffQueue db).find? (!skip ·) = some q →
      tid = (q.id : Int) := by
  have top : Queue.staffHead skip db = some tid ∧ ∀ x, (limits db e).2.2 = some x → ((limits db e).1 : Int) < x := by
    unfold Spawn.reserveTask at h
    split at h
    · rename_i db' r' hg
      unfold Spawn.reserveTask.go at hg
      simp only at hg
      split at hg
      · cases hg
      · rename_i htop
        simp only [bne_iff_ne, ne_eq, Decidable.not_not] at htop
        refine ⟨htop, ?_⟩
        simp only [Bind.bind, Except.bind] at hg
        split at hg
        · cases hg
        · rename_i db1 hr; exact reserveAgent_max hr
    · cases h
  refine ⟨top.1, top.2, ?_, fun q hr hq => ?_⟩
  · obtain ⟨t, ht, hi, hh, -⟩ := QueueProofs.staffHead_not_held top.1
    exact ⟨t, ht, hi, hh⟩
  · have := top.1.symm.trans (QueueProofs.staffHead_queue hr hq)
    exact Option.some.inj this

/-- Sp1 and Sp2 on the code: after a failed launch no claim of the new agent on its task remains, the task it held is
open with no owner (back in the pool at once), and the row, if no terminal took it, is ended. -/
theorem unreserve_spec (db : Db) (name : String) (r : Task) (now : Int) :
    (∀ t ∈ (Spawn.unreserve db name (some r) now).tasks, (t.id : Int) = r.id → t.owner = some name →
      t.state ≠ .claimed) ∧
    (∀ t ∈ db.tasks, (t.id : Int) = r.id → t.owner = some name → t.state = .claimed →
      { t with state := .open, owner := none, lease_until := none, first_claimed_at := r.first_claimed_at } ∈
        (Spawn.unreserve db name (some r) now).tasks) ∧
    (∀ a ∈ (Spawn.unreserve db name (some r) now).agents, a.name = name → a.hc = none → a.ended = some now) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht hi ho
    simp only [Spawn.unreserve, Db.set, Db.setAgent, List.mem_map] at ht
    obtain ⟨u, -, rfl⟩ := ht
    by_cases h1 : (u.id : Int) = r.id
    · by_cases h2 : (u.owner == some name && decide (u.state = .claimed)) = true
      · simp [h1, h2]
      · simp only [h1, h2, ↓reduceIte] at ho ⊢
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, not_and] at h2
        exact h2 ho
    · simp_all
  · intro t ht hi ho hs
    simp only [Spawn.unreserve, Db.set, Db.setAgent, List.mem_map]
    exact ⟨t, ht, by simp [hi, ho, hs]⟩
  · intro a ha hn hh
    simp only [Spawn.unreserve, Db.set, Db.setAgent, List.mem_map] at ha
    obtain ⟨b, -, rfl⟩ := ha
    by_cases e : b.name = name <;> by_cases hb : b.hc = none <;> simp_all

/-! ## Takeover: `Agents.bind` (`swarm join`, `--takeover`) -/

/-- bind checks the row it read: if the binding changed since, it refuses and changes nothing. -/
theorem bind_changed {db : Db} {name : String} {cwd hc model : Option String} {r : Binding} {now : Int}
    (h : binding db name ≠ r) : (bind db name cwd hc model r now).1 = db ∧ ∃ e, (bind db name cwd hc model r now).2 = .error e := by
  simp [Agents.bind, h]

/-- A bind that went through found the binding it read, and leaves every row of that name live and bound to `hc`; a
takeover of another live terminal is logged. -/
theorem bind_ok {db : Db} {name : String} {cwd hc model : Option String} {r : Binding} {now : Int}
    (h : (bind db name cwd hc model r now).2 = .ok ()) :
    binding db name = r ∧
      (∀ a ∈ (bind db name cwd hc model r now).1.agents, a.name = name → a.hc = hc ∧ a.ended = none) ∧
      ∀ old, boundTo r = some old → some old ≠ hc →
        ∃ e ∈ (bind db name cwd hc model r now).1.events, e.kind = some "takeover" ∧ e.agent = some name := by
  by_cases hb : binding db name = r
  · refine ⟨hb, ?_, ?_⟩
    · intro a ha hn
      simp only [Agents.bind, hb, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at ha
      split at ha
      · split at ha
        · simp only [Db.log, Db.setAgent, List.mem_map] at ha
          obtain ⟨b, -, rfl⟩ := ha
          by_cases e : b.name = name <;> simp_all
        · simp only [Db.setAgent, List.mem_map] at ha
          obtain ⟨b, -, rfl⟩ := ha
          by_cases e : b.name = name <;> simp_all
      · simp only [Db.setAgent, List.mem_map] at ha
        obtain ⟨b, -, rfl⟩ := ha
        by_cases e : b.name = name <;> simp_all
    · intro old ho hne
      simp only [Agents.bind, hb, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, ho]
      have : (some old != hc) = true := by simpa using hne
      rw [ite_eq_left this]
      simp [Db.log]
  · simp [Agents.bind, hb] at h

/-! ## R2: no exception escapes a guarded pass (App's `Guard`) -/

/-- Whatever a pass does, its run under App's `guard` returns normally, with no `Exit`: an exit and an IO error both
come back as the pass's error text (`iteration_safe`'s pcalls, on the code that runs). -/
theorem guard_ok {α : Type} (x : App α) (ctx : Ctx) (w : Void IO.RealWorld) :
    ∃ v w', (((Guard.guard x : App (Except String α)).run).run ctx) w = EST.Out.ok (.ok v) w' := by
  change ∃ v w', (EST.tryCatch (ε := IO.Error) (σ := IO.RealWorld) (α := Except Exit (Except String α))
    (EST.bind ((ExceptT.run x).run ctx) fun (r : Except Exit α) => match r with
      | .ok a => EST.pure (Except.ok (Except.ok a))
      | .error e => EST.pure (Except.ok (Except.error s!"exit {e.code}")))
    (fun e => EST.pure (Except.ok (Except.error (toString e))))) w = _
  simp only [EST.tryCatch, EST.bind, EST.pure]
  cases (ExceptT.run x).run ctx w with
  | ok r w1 => cases r <;> exact ⟨_, _, rfl⟩
  | error e w1 => exact ⟨_, _, rfl⟩

/-- The model's `bgStall` on the code (board #125): `Watchd.hungStep` calls a job tree hung only when agent `n`'s last
`job-cpu` checkpoint holds that same tree and is JOB_HUNG old, so a tree that used a CPU second, started or ended a
process since is never hung. -/
theorem hungStep_hung {db : Db} {n sig : String} {t : Int} (h : (Watchd.hungStep db n sig t).1 = true) :
    ∃ e, (db.events.filter fun e => e.agent == some n && e.kind == some "job-cpu").getLast? = some e ∧
      e.data = some sig ∧ Watchd.JOB_HUNG ≤ t - e.ts.getD 0 := by
  unfold Watchd.hungStep at h
  split at h
  · cases h
  · rename_i e he
    by_cases hd : e.data = some sig
    · simp only [hd, beq_self_eq_true, ite_true, decide_eq_true_eq] at h; exact ⟨e, he, hd, h⟩
    · simp [hd] at h

end SwarmLean.WatchdProofs

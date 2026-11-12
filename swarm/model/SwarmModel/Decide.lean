import SwarmModel.Model
import SwarmModel.PrWatch

/-! Lifted (rung 3, board #27): the Lua's pure decisions with a counterpart in the model, line for line on the rows
they read, and each proved to be the model's decision on its view of the state. `watchd.keeps` (reap: does a lapsed
claim's owner keep it), `watchd.fate` (lifecycle: keep, unclean, reuse or end an agent), `msgs.wakes` (the
waiter), `ci.pr_act` (watchd's poll of a PR, board #28, PrWatch.lean) and `watchd.end_why` (`swarm end`, board #46). A Lua nil, or a NULL column, is `none`; a read the Lua makes through a callback (`f.claims()`, `cold()`) is
its answer, a `Bool`: what the read returns is the SQL's, rung 4. `DecideCases.lean` writes random inputs with these
functions' answers, which `../lua/test/decide_model_spec.lua` checks the Lua against. -/

namespace Swarm.Decide

/-- the agent row's columns the decisions read -/
structure ARow where
  ended : Option Nat := none
  status : String := "idle"
  hc : Option String := none
  stay : Option String := none
  lastActive : Option Int := none
  ctx : Option Nat := none
  waiter : Option Nat := none
  deriving Repr, Inhabited, DecidableEq

/-- watchd's `nz`: nil and "" are false -/
def nz : Option String → Bool
  | some s => s != ""
  | none => false

/-- watchd.keeps(o, bg, live_addrs): `live` is the live addresses, `none` when hc can't tell -/
def keepsL (o : Option ARow) (bg : Bool) (live : Option (List String)) : Bool :=
  match o with
  | none => false
  | some o => o.ended.isNone && (o.status != "idle" || bg)
      && !(live.isSome && nz o.hc && !(live.getD []).contains (o.hc.getD ""))

/-- an hc terminal as lifecycle reads it -/
structure Term where
  cwd : Option String := none
  status : String := "idle"
  deriving Repr, Inhabited, DecidableEq

/-- fate's reads, `f` in the Lua: `ours` is `f.ours(x.cwd)`, `alive` is `f.alive(a.waiter)` -/
structure Facts where
  ours : Bool
  claims : Bool
  locks : Bool
  unlanded : Bool
  job : Bool
  pool : Nat
  passedOver : Bool
  alive : Bool
  deriving Repr, Inhabited, DecidableEq

/-- the Lua's nil, "unclean", "reuse", "end" -/
inductive Verdict where | keep | unclean | reuse | end_
  deriving DecidableEq, Repr, Inhabited

/-- agents.SMALL_CTX -/
def smallCtx : Nat := 40000

/-- watchd.fate(a, t, x, has_terms, f) -/
def fateL (a : ARow) (t : Int) (x : Option Term) (hasTerms : Bool) (f : Facts) : Verdict :=
  if nz a.stay || a.status != "idle" || decide (t - a.lastActive.getD 0 < 120) || x.any (fun x => nz x.cwd && !f.ours)
      || (nz a.hc && hasTerms && x.all fun x => x.status != "idle" && x.status != "done")
      || f.claims || f.locks then .keep
  else if f.unlanded then .unclean
  else if f.job then .keep
  else if decide (a.ctx.getD 0 < smallCtx) && decide (f.pool > 0) && !f.passedOver && a.waiter.isSome && f.alive then .reuse
  else .end_

/-- a msg row's columns the waiter reads -/
structure MRow where
  kind : String
  urgent : Option Nat := none
  deriving Repr, Inhabited, DecidableEq

def MRow.urg (r : MRow) : Bool := r.urgent.getD 0 != 0

/-- msgs.wakes(rows, cold): the waking rows and whether one is urgent, or nil -/
def wakesL (rows : List MRow) (cold : Bool) : Option (List MRow × Bool) :=
  let (wake, urgent) := rows.foldl (fun (w, u) r => if r.kind != "notice" || r.urg then (w ++ [r], u || r.urg) else (w, u))
    ([], false)
  if !wake.isEmpty && (urgent || !cold) then some (wake, urgent) else none

-- ---------- the model's view ----------

def statusOf : ASt → String
  | .working => "working" | .blocked => "blocked" | .ended => "ended" | .idle => "idle" | .unborn => "unborn"

/-- slot a's row as reap reads it: none before it is born; its terminal's address is its slot, none if unbound -/
def keepRow (c : Cfg) (a : Nat) (g : Agent) : Option ARow :=
  if g.st == .unborn then none
  else some { ended := if g.st == .ended then some 0 else none, status := statusOf g.st,
              hc := if c.unbound.contains a then none else some (toString a) }

/-- `hc ls`'s live addresses: every slot whose terminal hasn't died; none when hc can't tell -/
def liveOf (c : Cfg) (s : State) : Option (List String) :=
  if c.hcSees then some ((c.agents.filter fun a => !(s.agt a).dead).map toString) else none

/-- reap's decision is the model's `keeps`, on the current Cfg (`release` idle, `bgKeeps`), except for an owner whose
bound terminal hc no longer lists: the Lua reopens its task, the model keeps it until `reapGone` (`keeps_gap`) -/
theorem keeps_lifted {c : Cfg} {s : State} {a : Nat} (hr : c.release = .idle) (hb : c.bgKeeps = true)
    (ha : a < c.nagents) (hd : ¬(c.hcSees = true ∧ c.unbound.contains a = false ∧ (s.agt a).dead = true)) :
    keepsL (keepRow c a (s.agt a)) (s.agt a).bg (liveOf c s) = keeps c (s.agt a) := by
  have hlive : (s.agt a).dead = false → c.hcSees = true →
      ((c.agents.filter fun b => !(s.agt b).dead).map toString).contains (toString a) = true := by
    intro hd' _
    simp only [List.contains_iff_mem, List.mem_map, List.mem_filter, Cfg.agents, List.mem_range]
    exact ⟨a, ⟨ha, by simp [hd']⟩, rfl⟩
  simp only [keeps, hr, hb, Bool.true_and, keepsL, keepRow, liveOf, Agent.live]
  cases hst : (s.agt a).st <;> cases hdd : (s.agt a).dead <;> cases hs : c.hcSees <;>
    cases hu : c.unbound.contains a <;> simp_all [statusOf, nz]

/-- the gap: a working owner whose bound terminal is gone keeps its lapsed claim in the model, not in the Lua -/
theorem keeps_gap : ∃ (c : Cfg) (s : State),
    keepsL (keepRow c 0 (s.agt 0)) (s.agt 0).bg (liveOf c s) = false ∧ keeps c (s.agt 0) = true :=
  ⟨{}, { (default : State) with ag := [{ (default : Agent) with st := .working, dead := true }] }, by decide, by decide⟩

/-- slot a's row as lifecycle reads it at time t, with no hc terminals (as the replay): `aged` is idle 2 min, `big` a
context of SMALL_CTX or more, `waiter` a waiter pid that is alive (`Env.waiter_alive`) -/
def fateRow (g : Agent) (t : Int) : ARow :=
  { status := statusOf g.st, lastActive := some (if g.aged then t - 120 else t),
    ctx := some (if g.big then smallCtx else 0), waiter := if g.waiter then some 1 else none,
    ended := if g.st == .ended then some 0 else none, stay := if g.stay then some "s" else none }

/-- fate's reads on the model: its claims and locks, its unlanded work, its background job, the pool, and passed over
(told of the whole pool, nothing unread: the model has no notices) -/
def factsOf (c : Cfg) (s : State) (a : Nat) : Facts :=
  { ours := true, claims := holds s a, locks := lockHeld s a, unlanded := unlanded c s a, job := (s.agt a).bg,
    pool := (pool c s).length,
    passedOver := (pool c s).all (s.agt a).told.contains && (unread s a).isEmpty, alive := true }

/-- the model's lifecycle verdict on a -/
def modelFate (c : Cfg) (s : State) (a : Nat) : Verdict :=
  if !idleFree s a then .keep else if unlanded c s a then .unclean else if c.bgLives && (s.agt a).bg then .keep
  else if reusable c s a then .reuse else .end_

theorem fate_core (g : Agent) (t : Int) (h1 h2 h3 : Bool) (pl u : List Nat) :
    fateL (fateRow g t) t none false ⟨true, h1, h2, h3, g.bg, pl.length, pl.all g.told.contains && u.isEmpty, true⟩ =
      if !(g.st == .idle && g.aged && !g.stay && !h1 && !h2) then .keep else if h3 then .unclean else if g.bg then .keep
      else if !g.big && !pl.isEmpty && !(pl.all g.told.contains && u.isEmpty) && g.waiter then .reuse else .end_ := by
  have h120 : t - (t - 120) = 120 := by omega
  have hpl : (0 < pl.length) = (pl.isEmpty = false) := by cases pl <;> simp
  rcases g with ⟨st, _, big, aged, _, _, _, _, _, _, bg, _, _, _, _, _, _, _, _, stay, _, _⟩
  simp only [fateL, fateRow, nz, smallCtx, hpl]
  cases stay <;> cases st <;> cases aged <;> cases big <;> cases h1 <;> cases h2 <;> cases h3 <;> cases bg <;>
    simp_all [statusOf, Int.sub_self]

/-- lifecycle's verdict is the model's, on the current Cfg (`bgLives`, board #15, as the replay), for an agent between no read and its write -/
theorem fate_lifted {c : Cfg} {s : State} {a : Nat} {t : Int} (hp : c.passedOver = true) (hw : c.waiterAlive = true)
    (hb : c.bgLives = true) (hr : (s.agt a).reading = 0) (hs : (s.agt a).snap = []) :
    fateL (fateRow (s.agt a) t) t none false (factsOf c s a) = modelFate c s a := by
  rw [factsOf, fate_core, modelFate, reusable, finished, idleFree]
  simp only [hp, hw, hb, hr, hs, beq_self_eq_true, List.isEmpty_nil, Bool.and_true, Bool.not_true, Bool.or_false,
    Bool.true_and]
  cases h1 : holds s a <;> cases h2 : lockHeld s a <;> cases h3 : unlanded c s a <;>
    cases ((s.agt a).st == .idle && (s.agt a).aged) <;> cases (s.agt a).stay <;> cases (s.agt a).bg <;> simp

theorem fate_end {c : Cfg} {s : State} {a : Nat} {t : Int} (hp : c.passedOver = true) (hw : c.waiterAlive = true)
    (hb : c.bgLives = true) (hr : (s.agt a).reading = 0) (hs : (s.agt a).snap = []) :
    fateL (fateRow (s.agt a) t) t none false (factsOf c s a) = .end_ ↔ ends c s a = true := by
  rw [fate_lifted hp hw hb hr hs, modelFate, ends, finished, hb]
  cases idleFree s a <;> cases unlanded c s a <;> cases reusable c s a <;> cases (s.agt a).bg <;> simp

theorem fate_reuse {c : Cfg} {s : State} {a : Nat} {t : Int} (hp : c.passedOver = true) (hw : c.waiterAlive = true)
    (hb : c.bgLives = true) (hr : (s.agt a).reading = 0) (hs : (s.agt a).snap = []) :
    fateL (fateRow (s.agt a) t) t none false (factsOf c s a) = .reuse ↔ reusable c s a = true := by
  rw [fate_lifted hp hw hb hr hs, modelFate, hb]
  have : reusable c s a = true → finished c s a = true := fun h => by
    simp only [reusable, Bool.and_eq_true] at h; exact h.1.1.1.1
  cases hi : idleFree s a <;> cases hu : unlanded c s a <;> cases hre : reusable c s a <;> cases hg : (s.agt a).bg <;>
    simp_all [finished]

/-! H1 (board #46): `swarm end A` without --force, watchd.end_why: why it refuses, on fate's reads. -/

/-- watchd.end_why's answers: "is <status>", "stays for", "owns a claimed task", "holds a lock", "has a background job
running", "has work not on its base"; `none` is the Lua's nil (it ends the agent) -/
inductive Why where | status | stay | claims | locks | job | unlanded
  deriving DecidableEq, Repr, Inhabited

/-- watchd.end_why(a, f) -/
def endWhyL (a : ARow) (f : Facts) : Option Why :=
  if a.status != "idle" then some .status
  else if nz a.stay then some .stay
  else if f.claims then some .claims
  else if f.locks then some .locks
  else if f.job then some .job
  else if f.unlanded then some .unlanded
  else none

/-- `swarm end`'s check is the model's `endable` on the model's view of the agent (as lifecycle reads it) -/
theorem endWhy_lifted (c : Cfg) (s : State) (a : Nat) (t : Int) :
    (endWhyL (fateRow (s.agt a) t) (factsOf c s a)).isNone = endable c s a := by
  have hi : (statusOf (s.agt a).st != "idle") = !((s.agt a).st == .idle) := by cases (s.agt a).st <;> rfl
  simp only [endWhyL, fateRow, factsOf, endable, nz, hi]
  by_cases h0 : (s.agt a).st == .idle <;> by_cases h5 : (s.agt a).stay <;> by_cases h1 : holds s a <;>
    by_cases h2 : lockHeld s a <;> by_cases h3 : (s.agt a).bg <;> by_cases h4 : unlanded c s a <;>
    simp [h0, h1, h2, h3, h4, h5]

/-- whatever lifecycle would end or reuse, `swarm end` ends: its checks are among fate's, for any row, terminal and reads -/
theorem endWhy_of_fate {a : ARow} {t : Int} {x : Option Term} {h : Bool} {f : Facts}
    (hv : fateL a t x h f = .end_ ∨ fateL a t x h f = .reuse) : endWhyL a f = none := by
  simp only [fateL] at hv
  simp only [endWhyL]
  repeat' split at hv
  all_goals first | (rcases hv with hv | hv <;> cases hv) | skip
  all_goals simp_all

/-! F1 (board #41): what `swarm state --json` reports of an idle agent (its `fate`) is watchd's decision. The Lua runs
`watchd.fate` itself with `f.rec`, a recorder each check calls with its value; `f.all` makes no check hold, so every
check is made. `fateRec` is that recorder lifted, line for line: its verdict is `fateL` (`fateRec_verdict`, and so the
model's lifecycle verdict: `report_lifted`), each check it records is one of fate's inputs with that input's value
(`fateRec_vals`), the agent screen's run records every check (`fateRec_all`), and Home's short reason is the one check
that held, all before it false (`fateRec_short`). -/

/-- fate's checks, as watchd.fate's `k(label, v)` names them -/
inductive Check where | stay | idle | terminal | task | lock | unlanded | job | context | waiter
  deriving DecidableEq, Repr, Inhabited

/-- each check's value: the input of `fateL` it stands for -/
def Check.val (a : ARow) (t : Int) (x : Option Term) (hasTerms : Bool) (f : Facts) : Check → Bool
  | .stay => nz a.stay
  | .idle => a.status != "idle" || decide (t - a.lastActive.getD 0 < 120)
  | .terminal => x.any (fun x => nz x.cwd && !f.ours) || (nz a.hc && hasTerms && x.all fun x => x.status != "idle" && x.status != "done")
  | .task => f.claims
  | .lock => f.locks
  | .unlanded => f.unlanded
  | .job => f.job
  | .context => decide (a.ctx.getD 0 < smallCtx) && decide (f.pool > 0) && !f.passedOver
  | .waiter => a.waiter.isSome && f.alive

/-- every check, in the order fate makes them -/
def Check.order : List Check := [.stay, .idle, .terminal, .task, .lock, .unlanded, .job, .context, .waiter]

/-- the Lua's `or` chain of `k` calls: each check is recorded with its value; one that holds (`v and not all`) stops it -/
def orRec (val : Check → Bool) (all : Bool) : List Check → List (Check × Bool) × Bool
  | [] => ([], false)
  | k :: ks => if val k && !all then ([(k, true)], true) else let r := orRec val all ks; ((k, val k) :: r.1, r.2)

/-- watchd.fate run with f.rec (and f.all): its return and what it recorded, in order -/
def fateRecV (val : Check → Bool) (all : Bool) : Verdict × List (Check × Bool) :=
  let r1 := orRec val all [.stay, .idle, .terminal, .task, .lock]
  if r1.2 then (.keep, r1.1) else
  let r2 := r1.1 ++ [(.unlanded, val .unlanded)]
  if val .unlanded && !all then (.unclean, r2) else
  let r3 := r2 ++ [(.job, val .job)]
  if val .job && !all then (.keep, r3) else
  let r4 := r3 ++ [(.context, val .context), (.waiter, val .waiter)]
  if (val .waiter && !all) && (val .context && !all) then (.reuse, r4) else (.end_, r4)

def fateRec (a : ARow) (t : Int) (x : Option Term) (hasTerms : Bool) (f : Facts) (all : Bool) :
    Verdict × List (Check × Bool) :=
  fateRecV (Check.val a t x hasTerms f) all

/-- `fateL` is a function of the checks' values -/
theorem fateL_val (a : ARow) (t : Int) (x : Option Term) (hasTerms : Bool) (f : Facts) :
    fateL a t x hasTerms f = (let v := Check.val a t x hasTerms f
      if v .stay || v .idle || v .terminal || v .task || v .lock then .keep else if v .unlanded then .unclean
      else if v .job then .keep else if v .context && v .waiter then .reuse else .end_) := by
  simp only [fateL, Check.val, Bool.or_assoc, Bool.and_assoc]

/-- the verdict state --json reports is fate's -/
theorem fateRec_verdict (a : ARow) (t : Int) (x : Option Term) (hasTerms : Bool) (f : Facts) :
    (fateRec a t x hasTerms f false).1 = fateL a t x hasTerms f := by
  rw [fateL_val]
  simp only [fateRec, fateRecV, orRec, Bool.not_false, Bool.and_true]
  generalize Check.val a t x hasTerms f = v
  cases h1 : v .stay <;> try simp [h1]
  cases h2 : v .idle <;> try simp [h2]
  cases h3 : v .terminal <;> try simp [h3]
  cases h4 : v .task <;> try simp [h4]
  cases h5 : v .lock <;> try simp [h5]
  cases h6 : v .unlanded <;> try simp [h6]
  cases h7 : v .job <;> try simp [h7]
  cases v .context <;> cases v .waiter <;> rfl

/-- F1: the reported verdict is the model's lifecycle verdict, on the hypotheses of `fate_lifted` -/
theorem report_lifted {c : Cfg} {s : State} {a : Nat} {t : Int} (hp : c.passedOver = true) (hw : c.waiterAlive = true)
    (hb : c.bgLives = true) (hr : (s.agt a).reading = 0) (hs : (s.agt a).snap = []) :
    (fateRec (fateRow (s.agt a) t) t none false (factsOf c s a) false).1 = modelFate c s a := by
  rw [fateRec_verdict, fate_lifted hp hw hb hr hs]

theorem orRec_vals (val : Check → Bool) (all : Bool) (ks : List Check) : ∀ p ∈ (orRec val all ks).1, p.2 = val p.1 := by
  induction ks with
  | nil => simp [orRec]
  | cons k ks ih =>
    intro p hp
    simp only [orRec] at hp
    split at hp
    · simp only [List.mem_singleton] at hp; subst hp; simp_all
    · simp only [List.mem_cons] at hp; rcases hp with rfl | hp
      · rfl
      · exact ih p hp

/-- each check shown is one of fate's inputs, with its value -/
theorem fateRec_vals (a : ARow) (t : Int) (x : Option Term) (hasTerms : Bool) (f : Facts) (all : Bool) :
    ∀ p ∈ (fateRec a t x hasTerms f all).2, p.2 = p.1.val a t x hasTerms f := by
  have h := orRec_vals (Check.val a t x hasTerms f) all [.stay, .idle, .terminal, .task, .lock]
  intro p hp
  simp only [fateRec, fateRecV] at hp
  repeat' split at hp
  all_goals simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
  all_goals first
    | exact h p hp
    | (rcases hp with ((hp | rfl) | rfl) | rfl | rfl <;> first | exact h p hp | rfl)
    | (rcases hp with (hp | rfl) | rfl <;> first | exact h p hp | rfl)
    | (rcases hp with hp | rfl <;> first | exact h p hp | rfl)

/-- the agent screen's run (`f.all`) records every check, in order, each with its value -/
theorem fateRec_all (a : ARow) (t : Int) (x : Option Term) (hasTerms : Bool) (f : Facts) :
    (fateRec a t x hasTerms f true).2 = Check.order.map fun k => (k, k.val a t x hasTerms f) := by
  simp [fateRec, fateRecV, orRec, Check.order]

/-- Home's short reason: when fate keeps an agent before the reuse checks (keep or unclean), the plain run's last record
is the check that held, and every check before it is false: that check is what keeps it -/
theorem fateRec_short (a : ARow) (t : Int) (x : Option Term) (hasTerms : Bool) (f : Facts)
    (hv : (fateRec a t x hasTerms f false).1 = .keep ∨ (fateRec a t x hasTerms f false).1 = .unclean) :
    ∃ k, (fateRec a t x hasTerms f false).2.getLast? = some (k, true)
      ∧ ∀ p ∈ (fateRec a t x hasTerms f false).2.dropLast, p.2 = false := by
  simp only [fateRec, fateRecV, orRec, Bool.not_false, Bool.and_true] at hv ⊢
  generalize Check.val a t x hasTerms f = v at hv ⊢
  cases h1 : v .stay <;> try simp [h1] at hv ⊢
  cases h2 : v .idle <;> try simp [h2] at hv ⊢
  cases h3 : v .terminal <;> try simp [h3] at hv ⊢
  cases h4 : v .task <;> try simp [h4] at hv ⊢
  cases h5 : v .lock <;> try simp [h5] at hv ⊢
  cases h6 : v .unlanded <;> try simp [h6] at hv ⊢
  cases h7 : v .job <;> try simp [h7] at hv ⊢
  cases h8 : v .context <;> cases h9 : v .waiter <;> simp_all

def kindOf : Kind → String
  | .dm => "dm" | _ => "system"

/-- model message i as a msg row: none is a notice (notices go to the communicator, outside the model) -/
def msgRow (s : State) (i : Nat) : MRow := { kind := kindOf (s.msg i).kind, urgent := some (if (s.msg i).urgent then 1 else 0) }

theorem wakesL_all (rows : List MRow) (h : ∀ r ∈ rows, r.kind != "notice") (cold : Bool) :
    (wakesL rows cold).isSome = (!rows.isEmpty && (rows.any MRow.urg || !cold)) := by
  have : ∀ (l : List MRow) w u, (∀ r ∈ l, r.kind != "notice") →
      l.foldl (fun (w, u) r => if r.kind != "notice" || r.urg then (w ++ [r], u || r.urg) else (w, u)) (w, u)
        = (w ++ l, u || l.any MRow.urg) := by
    intro l; induction l with
    | nil => intro w u _; simp
    | cons r l ih =>
      intro w u hl
      simp only [List.foldl_cons, hl r (by simp), Bool.true_or, ↓reduceIte]
      rw [ih _ _ (fun x hx => hl x (by simp [hx]))]
      simp [Bool.or_assoc]
  simp only [wakesL, this rows [] false h, List.nil_append, Bool.false_or]
  split <;> simp_all

/-- the waiter wakes exactly when the model's `wakes` says, on the agent's unread messages and its `cold` -/
theorem wakes_lifted {s : State} {a : Nat} :
    (wakesL ((unread s a).map (msgRow s)) (s.agt a).cold).isSome = wakes s a := by
  rw [wakesL_all _ (by intro r hr; simp only [List.mem_map] at hr; obtain ⟨i, _, rfl⟩ := hr
                       simp only [msgRow]; cases (s.msg i).kind <;> decide)]
  simp only [wakes, List.isEmpty_map, List.any_map]
  have : (MRow.urg ∘ msgRow s) = fun i => (s.msg i).urgent := by
    funext i; simp only [Function.comp, MRow.urg, msgRow]; cases (s.msg i).urgent <;> rfl
  rw [this]; cases (unread s a).isEmpty <;> cases (s.agt a).cold <;> simp [Bool.or_comm]

open PrW

/-- the PR ci.pr_act reads: gh's state and ci.verdict of its checks -/
structure PrRow where
  state : String
  verdict : String
  deriving Repr, Inhabited, DecidableEq

inductive PrAct where | done | wake
  deriving Repr, Inhabited, DecidableEq

/-- ci.pr_act(pr, gated, told) -/
def prActL (pr : PrRow) (gated told : Bool) : Option PrAct :=
  if pr.state == "MERGED" then some .done
  else if gated && pr.state == "OPEN" && pr.verdict != "pending" && !told then some .wake
  else none

/-- the model's PR of task k as gh shows it -/
def prRow (k : PTask) : PrRow := { state := if k.pr.merged then "MERGED" else "OPEN", verdict := k.pr.checks.name }

/-- what the poll does to task k on the Lua's decision: done, told, or nothing -/
def applyAct (k : PTask) : Option PrAct → PTask
  | some .done => { k with st := .done }
  | some .wake => { k with pr := { k.pr with told := true } }
  | none => k

/-- watchd's poll of a claimed task with a PR, with the fix on, does what ci.pr_act decides on the PR as gh shows it -/
theorem prAct_lifted {c : PCfg} (hw : c.wakeFix = true) (hc : c.closeFix = true) {k : PTask} (hs : k.st = .claimed)
    (ho : k.pr.opened = true) : pollTask c k = applyAct k (prActL (prRow k) c.gated k.pr.told) := by
  cases hm : k.pr.merged <;> cases hk : k.pr.checks <;> cases hg : c.gated <;> cases ht : k.pr.told <;>
    simp [pollTask, prActL, prRow, applyAct, Checks.name, hs, ho, hm, hk, hg, ht, hw, hc]

end Swarm.Decide

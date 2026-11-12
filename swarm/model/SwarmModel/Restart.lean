import SwarmModel.Comms

/-! R1 (board #49): `swarm watchd --restart` keeps exactly one watchd. The world is Comms.lean's, with each swarm's
watchd record (meta.watchd, a pid), meta.watchd_up, the watchd processes, and the restart waiting for the one it started
(`restart`, `takeover`, `crash`, `loop`, `rpoll`, `rok`, `rfail`). `waitUp` is board #41's handover; finding #34
(Findings.lean) is the run that breaks (b) without it.

- (a) at most one watchd ticks a swarm: the record's, running (`R1a_of`). Structural, as a tick is one step here: in
  the Lua the loop reads the record and then ticks, so a takeover between the two lets the old one finish one tick
  beside the new one's first (not modelled).
- (b) the loop ends a watchd only when the record names another that runs and has ticked, and the restart reports
  success only then (`R1b_of`, with `waitUp`; `not_R1b`, finding #34, without).
- (c) on a fair run a watchd that keeps running gets its swarm ticked at infinitely many steps (`R1c_of`); so does the
  one a restart starts (`restart_ticks`). -/

namespace Swarm

/-- process p is swarm i's -/
def World.isOf (w : World) (i p : Nat) : Prop := p < w.wds.length ∧ (w.proc p).sw = i

/-- the watchd that ticks swarm i: the record's, running -/
def ticker (w : World) (i p : Nat) : Bool := w.wdOf i == some p && w.alive p

/-- R1 (a): in every reachable world at most one watchd ticks a swarm, and it is that swarm's -/
def R1a (c : CCfg) : Prop :=
  ∀ w i, CReachable c w → (∀ p q, ticker w i p = true → ticker w i q = true → p = q) ∧
    ∀ p, ticker w i p = true → w.isOf i p

/-- R1 (b): never zero once there was one. A watchd's loop ends it only when the record names another watchd, running,
that meta.watchd_up names and that has ticked; and `--restart` reports success only when that holds -/
def R1b (c : CCfg) : Prop :=
  (∀ w w' p, CReachable c w → cstep c w (.loop p) = some w' → w'.alive p = false →
    ∃ q, q ≠ p ∧ w'.wdOf (w.proc p).sw = some q ∧ w'.alive q = true ∧ w'.upOf (w.proc p).sw = some q ∧
      (w'.proc q).ticked = true) ∧
  (∀ w w' i, CReachable c w → cstep c w (.rok i) = some w' →
    ∃ q, w'.wdOf i = some q ∧ w'.alive q = true ∧ w'.upOf i = some q ∧ (w'.proc q).ticked = true)

/-- the watchd processes' own steps are fair: a takeover or loop step enabled at infinitely many steps is taken at
infinitely many (hc's `run --bg` starts the program, `HcRunStarts`; a running loop goes round every interval) -/
def CRun.FairWd {c : CCfg} (r : CRun c) : Prop :=
  ∀ a, (∃ p, a = CAction.takeover p ∨ a = .loop p) → (∀ N, ∃ n ≥ N, (cstep c (r.st n) a).isSome) → ∀ N, ∃ n ≥ N, r.act n = a

-- ---------- lists ----------

theorem R.getD_append_one {α : Type} (l : List α) (x d : α) (p : Nat) :
    (l ++ [x]).getD p d = if p < l.length then l.getD p d else if p = l.length then x else d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append]
  split
  · rfl
  · rename_i h; split
    · subst_vars; simp
    · rename_i h'
      have : p - l.length ≠ 0 := by omega
      simp [this]

theorem R.getD_modify {α : Type} (l : List α) (f : α → α) (q p : Nat) (d : α) :
    (l.modify q f).getD p d = if p = q ∧ q < l.length then f (l.getD p d) else l.getD p d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_modify]
  by_cases h : p = q
  · subst h; by_cases hq : p < l.length
    · simp [hq]
    · simp [hq]
  · simp [h, Ne.symm h]

theorem R.getD_set {α : Type} (l : List α) (i : Nat) (v : α) (j : Nat) (d : α) :
    (l.set i v).getD j d = if j = i ∧ i < l.length then v else l.getD j d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h : i = j
  · subst h; by_cases hi : i < l.length <;> simp [hi]
  · simp [h, Ne.symm h]

-- ---------- what each step does to the processes ----------

theorem lt_of_alive {w : World} {p : Nat} (h : w.alive p = true) : p < w.wds.length := by
  refine Nat.lt_of_not_le fun hl => ?_
  have : (default : Wd).on = false := rfl
  simp [World.alive, World.proc, List.getD_eq_getElem?_getD, List.getElem?_eq_none hl, this] at h

theorem proc_append (w : World) (d : Wd) (p : Nat) (h : p < w.wds.length) :
    ({ w with wds := w.wds ++ [d] } : World).proc p = w.proc p := by
  simp only [World.proc]; rw [R.getD_append_one]; simp [h]

theorem proc_modify (w : World) (f : Wd → Wd) (q p : Nat) :
    ({ w with wds := w.wds.modify q f } : World).proc p = if p = q ∧ q < w.wds.length then f (w.proc p) else w.proc p := by
  simp only [World.proc]; rw [R.getD_modify]

theorem wdTicked_wds (w : World) (i : Nat) :
    (wdTicked w i).wds = w.wds ∨ ∃ p, (wdTicked w i).wds = w.wds.modify p ({ · with ticked := true }) := by
  unfold wdTicked; split
  · split
    · exact .inl rfl
    · exact .inr ⟨_, rfl⟩
  · exact .inl rfl

theorem tickW_wds (c : CCfg) (w : World) (i : Nat) : (tickW c w i).wds = w.wds ∧ (tickW c w i).wd = w.wd ∧
    (tickW c w i).up = w.up ∧ (tickW c w i).rs = w.rs := by
  simp only [tickW]; repeat' split
  all_goals exact ⟨rfl, rfl, rfl, rfl⟩

/-- a step keeps every process's swarm and terminal, and only adds processes -/
theorem wds_step {c : CCfg} {w w' : World} {a : CAction} (h : cstep c w a = some w') :
    w.wds.length ≤ w'.wds.length ∧ ∀ p, p < w.wds.length → (w'.proc p).sw = (w.proc p).sw ∧ (w'.proc p).term = (w.proc p).term := by
  have hmod : ∀ (f : Wd → Wd), (∀ d, (f d).sw = d.sw ∧ (f d).term = d.term) → ∀ (w1 : World) q, w1.wds = w.wds.modify q f →
      w.wds.length ≤ w1.wds.length ∧ ∀ p, p < w.wds.length → (w1.proc p).sw = (w.proc p).sw ∧ (w1.proc p).term = (w.proc p).term := by
    intro f hf w1 q hw
    refine ⟨by simp [hw], fun p _ => ?_⟩
    have : w1.proc p = ({ w with wds := w.wds.modify q f } : World).proc p := by simp [World.proc, hw]
    rw [this, proc_modify]; split
    · exact hf _
    · exact ⟨rfl, rfl⟩
  have hsame : ∀ w1 : World, w1.wds = w.wds →
      w.wds.length ≤ w1.wds.length ∧ ∀ p, p < w.wds.length → (w1.proc p).sw = (w.proc p).sw ∧ (w1.proc p).term = (w.proc p).term :=
    fun w1 hw => ⟨by simp [hw], fun p _ => by simp [World.proc, hw]⟩
  have happ : ∀ (d : Wd) (w1 : World), w1.wds = w.wds ++ [d] →
      w.wds.length ≤ w1.wds.length ∧ ∀ p, p < w.wds.length → (w1.proc p).sw = (w.proc p).sw ∧ (w1.proc p).term = (w.proc p).term := by
    intro d w1 hw
    refine ⟨by simp [hw], fun p hp => ?_⟩
    have : w1.proc p = ({ w with wds := w.wds ++ [d] } : World).proc p := by simp [World.proc, hw]
    rw [this, proc_append _ _ _ hp]; exact ⟨rfl, rfl⟩
  cases a with
  | sw i act =>
    simp only [cstep] at h; split at h; · simp at h
    obtain ⟨s, -, rfl⟩ := Option.map_eq_some_iff.mp h; exact hsame _ rfl
  | «open» => simp only [cstep, Option.some.injEq] at h; subst h; exact hsame _ rfl
  | join => simp only [cstep, cjoin, cwhen] at h; split at h <;> simp at h; subst h; exact hsame _ rfl
  | watchd => simp only [cstep, startWd, cwhen] at h; split at h <;> simp at h; subst h; exact happ _ _ rfl
  | die => simp only [cstep, cdie, cwhen] at h; split at h <;> simp at h; subst h; exact hsame _ rfl
  | tick i =>
    simp only [cstep, cwhen] at h; split at h <;> simp at h; subst h
    rcases wdTicked_wds (tickW c w i) i with e | ⟨p, e⟩ <;> rw [(tickW_wds c w i).1] at e
    · exact hsame _ e
    · exact hmod (fun x => { x with ticked := true }) (fun _ => ⟨rfl, rfl⟩) _ _ e
  | restart => simp only [cstep, restart, cwhen] at h; split at h <;> simp at h; subst h; exact happ _ _ rfl
  | takeover => simp only [cstep, takeover, cwhen] at h; split at h <;> simp at h; subst h; exact hmod (fun x => { x with took := true }) (fun _ => ⟨rfl, rfl⟩) _ _ rfl
  | crash => simp only [cstep, crash, cwhen, stopWd] at h; split at h <;> simp at h; subst h; exact hmod (fun x => { x with on := false }) (fun _ => ⟨rfl, rfl⟩) _ _ rfl
  | loop =>
    simp only [cstep, loop, stopWd] at h
    repeat' split at h
    all_goals simp only [reduceCtorEq, Option.some.injEq] at h
    all_goals subst h
    all_goals first | exact hsame _ rfl | exact hmod (fun x => { x with on := false }) (fun _ => ⟨rfl, rfl⟩) _ _ rfl
  | rpoll => simp only [cstep, rpoll, cwhen] at h; repeat' split at h
             all_goals simp only [reduceCtorEq, Option.some.injEq] at h
             all_goals subst h; exact hsame _ rfl
  | rok => simp only [cstep, rok, cwhen] at h; repeat' split at h
           all_goals simp only [reduceCtorEq, Option.some.injEq] at h
           all_goals subst h; exact hsame _ rfl
  | rfail =>
    simp only [cstep, rfail, stopWd] at h
    repeat' split at h
    all_goals simp only [reduceCtorEq, Option.some.injEq] at h
    all_goals subst h
    all_goals first | exact hsame _ rfl | exact hmod (fun x => { x with on := false }) (fun _ => ⟨rfl, rfl⟩) _ _ rfl

theorem isOf_step {c : CCfg} {w w' : World} {a : CAction} (h : cstep c w a = some w') {i p : Nat} (hp : w.isOf i p) :
    w'.isOf i p :=
  have ⟨hl, hs⟩ := wds_step h
  ⟨Nat.lt_of_lt_of_le hp.1 hl, (hs p hp.1).1.trans hp.2⟩

theorem CRun.isOf {c : CCfg} (r : CRun c) {i p n : Nat} (h : (r.st n).isOf i p) : ∀ m ≥ n, (r.st m).isOf i p := by
  intro m hm
  induction m with
  | zero => have : n = 0 := by omega
            exact this ▸ h
  | succ m ih =>
    by_cases e : n = m + 1
    · exact e ▸ h
    · exact isOf_step (r.ok m) (ih (by omega))

-- ---------- the invariant ----------

structure WdInv (c : CCfg) (w : World) : Prop where
  wdLen : w.wd.length = c.nswarms
  swLt : ∀ p, p < w.wds.length → (w.proc p).sw < c.nswarms
  /-- the record names a process of its swarm -/
  rcd : ∀ i p, w.wdOf i = some p → w.isOf i p
  /-- meta.watchd_up names a process of its swarm that has ticked -/
  upr : ∀ i p, w.upOf i = some p → w.isOf i p ∧ (w.proc p).ticked = true
  /-- a swarm with a watchd process has a record -/
  hasRec : ∀ p, p < w.wds.length → (w.wdOf (w.proc p).sw).isSome = true
  /-- the record a restart gives back names a process of its swarm -/
  old : ∀ i r p, w.rsOf i = some r → r.old = some p → w.isOf i p

theorem wdOf_set (w : World) (i j : Nat) (v : Option Nat) :
    ({ w with wd := w.wd.set i v } : World).wdOf j = if j = i ∧ i < w.wd.length then v else w.wdOf j := by
  simp only [World.wdOf]; rw [R.getD_set]

theorem wdinv_init (c : CCfg) : WdInv c (cinit c) where
  wdLen := by simp [cinit, CCfg.swarms]
  swLt := by simp [cinit]
  rcd := by intro i p h; cases e : (List.range c.nswarms)[i]? <;> simp [cinit, World.wdOf, CCfg.swarms, List.getD_eq_getElem?_getD, e] at h
  upr := by intro i p h; cases e : (List.range c.nswarms)[i]? <;> simp [cinit, World.upOf, CCfg.swarms, List.getD_eq_getElem?_getD, e] at h
  hasRec := by simp [cinit]
  old := by intro i r p h; cases e : (List.range c.nswarms)[i]? <;> simp [cinit, World.rsOf, CCfg.swarms, List.getD_eq_getElem?_getD, e] at h

/-- a step that leaves the record, meta.watchd_up and the restarts alone, and each process's swarm and ticked -/
theorem wdinv_frame {c : CCfg} {w w' : World} (h : WdInv c w) (e1 : w'.wd = w.wd) (e3 : w'.up = w.up) (e4 : w'.rs = w.rs)
    (hl : w'.wds.length = w.wds.length)
    (hp : ∀ p, (w'.proc p).sw = (w.proc p).sw ∧ ((w.proc p).ticked = true → (w'.proc p).ticked = true)) :
    WdInv c w' := by
  have hw : ∀ i, w'.wdOf i = w.wdOf i := fun i => by simp [World.wdOf, e1]
  have hi : ∀ i p, w'.isOf i p ↔ w.isOf i p := fun i p => by simp [World.isOf, hl, (hp p).1]
  refine ⟨e1 ▸ h.wdLen, fun p hq => (hp p).1 ▸ h.swLt p (hl ▸ hq), fun i p hr => (hi i p).2 (h.rcd i p (hw i ▸ hr)),
    fun i p hu => ?_, fun p hq => by rw [(hp p).1, hw]; exact h.hasRec p (hl ▸ hq),
    fun i r p hr ho => (hi i p).2 (h.old i r p (by simpa [World.rsOf, e4] using hr) ho)⟩
  have := h.upr i p (by simpa [World.upOf, e3] using hu)
  exact ⟨(hi i p).2 this.1, (hp p).2 this.2⟩

theorem wdinv_stop {c : CCfg} {w : World} (h : WdInv c w) (p : Nat) : WdInv c (stopWd w p) :=
  wdinv_frame h rfl rfl rfl (by simp [stopWd]) fun q => by
    simp only [stopWd, proc_modify]; split <;> exact ⟨rfl, id⟩

/-- the record set to a process of its swarm -/
theorem wdinv_setRec {c : CCfg} {w : World} (h : WdInv c w) {i p : Nat} (hp : w.isOf i p) :
    WdInv c { w with wd := w.wd.set i (some p) } := by
  refine ⟨by simp [h.wdLen], h.swLt, fun j q hq => ?_, h.upr, fun q hq => ?_, h.old⟩
  · rw [wdOf_set] at hq; split at hq
    · rename_i e; obtain ⟨rfl, -⟩ := e; cases hq; exact hp
    · exact h.rcd j q hq
  · show (({ w with wd := w.wd.set i (some p) } : World).wdOf (w.proc q).sw).isSome = true
    rw [wdOf_set]; split
    · rfl
    · exact h.hasRec q hq

theorem isOf_grow {w w' : World} (hl : w.wds.length ≤ w'.wds.length) (hp : ∀ q, q < w.wds.length → w'.proc q = w.proc q)
    {i p : Nat} (h : w.isOf i p) : w'.isOf i p := ⟨Nat.lt_of_lt_of_le h.1 hl, by rw [hp p h.1]; exact h.2⟩

theorem upOf_set (w : World) (i j : Nat) (v : Option Nat) :
    ({ w with up := w.up.set i v } : World).upOf j = if j = i ∧ i < w.up.length then v else w.upOf j := by
  simp only [World.upOf]; rw [R.getD_set]
theorem rsOf_set (w : World) (i j : Nat) (v : Option Rst) :
    ({ w with rs := w.rs.set i v } : World).rsOf j = if j = i ∧ i < w.rs.length then v else w.rsOf j := by
  simp only [World.rsOf]; rw [R.getD_set]

/-- a new watchd process d whose swarm has a record -/
theorem wdinv_append {c : CCfg} {w : World} (h : WdInv c w) (d : Wd) (hd : d.sw < c.nswarms) (hr : (w.wdOf d.sw).isSome = true) :
    WdInv c { w with wds := w.wds ++ [d] } := by
  have hp : ∀ q, q < w.wds.length → ({ w with wds := w.wds ++ [d] } : World).proc q = w.proc q := fun q hq => proc_append _ _ _ hq
  have hn : ({ w with wds := w.wds ++ [d] } : World).proc w.wds.length = d := by simp only [World.proc]; rw [R.getD_append_one]; simp
  have hg : ∀ {i p}, w.isOf i p → ({ w with wds := w.wds ++ [d] } : World).isOf i p := fun e => isOf_grow (by simp) hp e
  have hq : ∀ q, q < (w.wds ++ [d]).length → q < w.wds.length ∨ q = w.wds.length := fun q hq => by simp at hq; omega
  refine ⟨h.wdLen, fun q hl => ?_, fun j q e => hg (h.rcd j q e), fun j q e => ?_, fun q hl => ?_, fun j r q e o => hg (h.old j r q e o)⟩
  · rcases hq q hl with e | rfl
    · rw [hp q e]; exact h.swLt q e
    · rw [hn]; exact hd
  · have := h.upr j q e; exact ⟨hg this.1, by rw [hp q this.1.1]; exact this.2⟩
  · rcases hq q hl with e | rfl
    · rw [hp q e]; exact h.hasRec q e
    · rw [hn]; exact hr

/-- a restart's wait set: its old record a process of its swarm -/
theorem wdinv_setRs {c : CCfg} {w : World} (h : WdInv c w) {i : Nat} {v : Option Rst}
    (hv : ∀ r p, v = some r → r.old = some p → w.isOf i p) : WdInv c { w with rs := w.rs.set i v } := by
  refine ⟨h.wdLen, h.swLt, h.rcd, h.upr, h.hasRec, fun j r p e o => ?_⟩
  rw [rsOf_set] at e; split at e
  · rename_i ej; obtain ⟨rfl, -⟩ := ej; exact hv r p e o
  · exact h.old j r p e o

/-- a watchd started by hand: a new process that writes the record -/
theorem wdinv_start {c : CCfg} {w : World} (h : WdInv c w) {i : Nat} (d : Wd) (hd : d.sw = i) (hi : i < c.nswarms) :
    WdInv c { w with wd := w.wd.set i (some w.wds.length), wds := w.wds ++ [d] } := by
  have hp : ∀ q, q < w.wds.length →
      ({ w with wd := w.wd.set i (some w.wds.length), wds := w.wds ++ [d] } : World).proc q = w.proc q := fun q hq => by
    simp only [World.proc]; rw [R.getD_append_one]; simp [hq]
  have hn : ({ w with wd := w.wd.set i (some w.wds.length), wds := w.wds ++ [d] } : World).proc w.wds.length = d := by
    simp only [World.proc]; rw [R.getD_append_one]; simp
  have hg : ∀ {j q}, w.isOf j q → ({ w with wd := w.wd.set i (some w.wds.length), wds := w.wds ++ [d] } : World).isOf j q :=
    fun e => isOf_grow (by simp) hp e
  have hq : ∀ q, q < (w.wds ++ [d]).length → q < w.wds.length ∨ q = w.wds.length := fun q hq => by simp at hq; omega
  have hw : ∀ j, ({ w with wd := w.wd.set i (some w.wds.length), wds := w.wds ++ [d] } : World).wdOf j =
      if j = i then some w.wds.length else w.wdOf j := by
    intro j; simp only [World.wdOf]; rw [R.getD_set]; simp [h.wdLen, hi]
  refine ⟨by simp [h.wdLen], fun q hl => ?_, fun j q e => ?_, fun j q e => ?_, fun q hl => ?_, fun j r q e o => hg (h.old j r q e o)⟩
  · rcases hq q hl with e | rfl
    · rw [hp q e]; exact h.swLt q e
    · rw [hn, hd]; exact hi
  · rw [hw] at e; split at e
    · subst_vars; cases e; exact ⟨by simp, by rw [hn]⟩
    · exact hg (h.rcd j q e)
  · have := h.upr j q e; exact ⟨hg this.1, by rw [hp q this.1.1]; exact this.2⟩
  · rcases hq q hl with e | rfl
    · rw [hp q e, hw]; split
      · rfl
      · exact h.hasRec q e
    · rw [hn, hw, hd]; simp

theorem wdinv_mod {c : CCfg} {w : World} (h : WdInv c w) (q : Nat) (f : Wd → Wd)
    (hf : ∀ d, (f d).sw = d.sw ∧ (d.ticked = true → (f d).ticked = true)) : WdInv c { w with wds := w.wds.modify q f } :=
  wdinv_frame h rfl rfl rfl (by simp) fun p => by
    simp only [proc_modify]; split
    · exact hf _
    · exact ⟨rfl, id⟩

theorem wdinv_ticked {c : CCfg} {w : World} (h : WdInv c w) (i : Nat) : WdInv c (wdTicked w i) := by
  unfold wdTicked; split
  · rename_i p hr; split
    · exact h
    · have hm := wdinv_mod h p (fun x => { x with ticked := true }) fun _ => ⟨rfl, fun _ => rfl⟩
      have hof := h.rcd i p hr
      refine ⟨hm.wdLen, hm.swLt, hm.rcd, fun j q e => ?_, hm.hasRec, hm.old⟩
      have e' : ({ w with wds := w.wds.modify p fun x => { x with ticked := true } } : World).upOf j = some q ∨
          (j = i ∧ q = p) := by
        rw [show ({ w with wds := w.wds.modify p (fun x => { x with ticked := true }), up := w.up.set i (some p) } : World)
          = { ({ w with wds := w.wds.modify p fun x => { x with ticked := true } } : World) with up := w.up.set i (some p) }
          from rfl, upOf_set] at e
        split at e
        · rename_i ej; cases e; exact .inr ⟨ej.1, rfl⟩
        · exact .inl e
      rcases e' with e' | ⟨rfl, rfl⟩
      · exact hm.upr j q e'
      · refine ⟨⟨by simp [hof.1], ?_⟩, ?_⟩
        · show ((({ w with wds := w.wds.modify q fun x => { x with ticked := true } } : World)).proc q).sw = j
          rw [proc_modify]; simp [hof.1, hof.2]
        · show ((({ w with wds := w.wds.modify q fun x => { x with ticked := true } } : World)).proc q).ticked = true
          rw [proc_modify]; simp [hof.1]
  · exact h

theorem wdinv_step {c : CCfg} {w w' : World} {a : CAction} (h : WdInv c w) (hs : cstep c w a = some w') : WdInv c w' := by
  cases a with
  | sw i act =>
    simp only [cstep] at hs; split at hs; · simp at hs
    obtain ⟨s, -, rfl⟩ := Option.map_eq_some_iff.mp hs
    exact wdinv_frame h rfl rfl rfl rfl fun _ => ⟨rfl, id⟩
  | «open» => simp only [cstep, Option.some.injEq] at hs; subst hs; exact wdinv_frame h rfl rfl rfl rfl fun _ => ⟨rfl, id⟩
  | join => simp only [cstep, cjoin, cwhen] at hs; split at hs <;> simp at hs; subst hs
            exact wdinv_frame h rfl rfl rfl rfl fun _ => ⟨rfl, id⟩
  | die => simp only [cstep, cdie, cwhen] at hs; split at hs <;> simp at hs; subst hs
           exact wdinv_frame h rfl rfl rfl rfl fun _ => ⟨rfl, id⟩
  | watchd i x =>
    simp only [cstep, startWd, cwhen] at hs; split at hs <;> simp at hs; subst hs
    rename_i hg; simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
    exact wdinv_start h _ rfl hg.1.1
  | tick i =>
    simp only [cstep, cwhen] at hs; split at hs <;> simp at hs; subst hs
    obtain ⟨e1, e2, e3, e4⟩ := tickW_wds c w i
    exact wdinv_ticked (wdinv_frame h e2 e3 e4 (by rw [e1]) fun p => by simp [World.proc, e1]) i
  | restart i x =>
    simp only [cstep, restart, cwhen] at hs; split at hs <;> simp at hs; subst hs
    rename_i hg; simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
    have ha := wdinv_append h ⟨i, x, true, false, false⟩ hg.1.1.1 hg.1.2
    have hp : ∀ q, q < w.wds.length → ({ w with wds := w.wds ++ [⟨i, x, true, false, false⟩] } : World).proc q = w.proc q :=
      fun q hq => proc_append _ _ _ hq
    exact wdinv_setRs ha fun r p e o => by
      simp only [Option.some.injEq] at e; subst e
      exact isOf_grow (by simp) hp (h.rcd i p o)
  | takeover p =>
    simp only [cstep, takeover, cwhen] at hs; split at hs <;> simp at hs; subst hs
    rename_i hg; simp only [Bool.and_eq_true] at hg
    have hm := wdinv_mod h p (fun x => { x with took := true }) fun _ => ⟨rfl, id⟩
    have hl := lt_of_alive hg.1
    have hs : (({ w with wds := w.wds.modify p fun x => { x with took := true } } : World).proc p).sw = (w.proc p).sw := by
      rw [proc_modify]; simp [hl]
    exact wdinv_setRec hm ⟨by simpa using hl, hs⟩
  | crash p =>
    simp only [cstep, crash, cwhen] at hs; split at hs <;> simp at hs; subst hs; exact wdinv_stop h p
  | loop p =>
    simp only [cstep, loop] at hs
    split at hs; · simp at hs
    rename_i hg; simp only [Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true] at hg
    split at hs
    · simp only [Option.some.injEq] at hs; subst hs; exact wdinv_stop h p
    · split at hs; · simp at hs
      split at hs
      · simp only [Option.some.injEq] at hs; subst hs; exact wdinv_stop h p
      · split at hs
        · simp only [Option.some.injEq] at hs; subst hs; exact wdinv_setRec h ⟨lt_of_alive hg.1, rfl⟩
        · simp at hs
  | rpoll i =>
    simp only [cstep, rpoll] at hs
    split at hs
    · rename_i r s hr _
      simp only [cwhen] at hs; split at hs <;> simp at hs; subst hs
      exact wdinv_setRs h fun r' p e o => by
        simp only [Option.some.injEq] at e; subst e; exact h.old i r p hr o
    · simp at hs
  | rok i =>
    simp only [cstep, rok] at hs
    split at hs
    · simp only [cwhen] at hs; split at hs <;> simp at hs; subst hs
      exact wdinv_setRs h fun _ _ e => by simp at e
    · simp at hs
  | rfail i =>
    simp only [cstep, rfail] at hs
    split at hs
    · rename_i r hr
      simp only [Option.some.injEq] at hs; subst hs
      split
      · rename_i s _
        have hst := wdinv_stop h s
        have hx : WdInv c { stopWd w s with wd := if (w.wdOf i == some s && r.old.isSome) = true then w.wd.set i r.old else w.wd } := by
          split
          · rename_i hc; simp only [Bool.and_eq_true, Option.isSome_iff_exists] at hc
            obtain ⟨q, hq⟩ := hc.2
            rw [hq]
            have ho := h.old i r q hr hq
            exact wdinv_setRec hst ⟨by simpa [stopWd] using ho.1, by simp only [stopWd, proc_modify]; split <;> exact ho.2⟩
          · exact hst
        exact wdinv_setRs hx fun _ _ e => by simp at e
      · exact wdinv_setRs h fun _ _ e => by simp at e
    · simp at hs

theorem wdinv_of_reachable {c : CCfg} {w : World} (h : CReachable c w) : WdInv c w := by
  induction h with
  | init => exact wdinv_init c
  | step _ _ hs ih => exact wdinv_step ih hs

theorem proc_stop {w : World} {p q : Nat} (h : q ≠ p) : (stopWd w p).proc q = w.proc q := by
  simp only [stopWd, proc_modify]; simp [h]
theorem alive_stop {w : World} {p q : Nat} (h : q ≠ p) : (stopWd w p).alive q = w.alive q := by
  simp only [World.alive, proc_stop h]; rfl
theorem alive_stop_self (w : World) (p : Nat) : (stopWd w p).alive p = false := by
  have : ((stopWd w p).proc p).on = false := by
    simp only [stopWd, proc_modify]; split
    · rfl
    · rename_i hn; simp only [World.proc, List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_none (by simp at hn; omega)]; rfl
  simp [World.alive, this]

-- ---------- R1 ----------

/-- R1 (a) -/
theorem R1a_of (c : CCfg) : R1a c := by
  intro w i hr
  refine ⟨fun p q hp hq => ?_, fun p hp => ?_⟩
  · simp only [ticker, Bool.and_eq_true, beq_iff_eq] at hp hq
    rw [hp.1] at hq; exact Option.some.inj hq.1
  · simp only [ticker, Bool.and_eq_true, beq_iff_eq] at hp
    exact (wdinv_of_reachable hr).rcd i p hp.1

/-- R1 (b), with board #41's handover -/
theorem R1b_of (c : CCfg) (hc : c.waitUp = true) : R1b c := by
  refine ⟨fun w w' p hr hs hdead => ?_, fun w w' i hr hs => ?_⟩
  · have h := wdinv_of_reachable hr
    simp only [cstep, loop] at hs
    split at hs; · simp at hs
    rename_i hg; simp only [Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true] at hg
    split at hs
    · rename_i hn; have := h.hasRec p (lt_of_alive hg.1); rw [hn] at this; simp at this
    · rename_i q hq
      split at hs; · simp at hs
      rename_i hqp
      have hq' : q ≠ p := by simpa using hqp
      split at hs
      · rename_i hw
        simp only [Option.some.injEq] at hs; subst hs
        simp only [hc, Bool.not_true, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at hw
        refine ⟨q, hq', hq, by rw [alive_stop hq']; exact hw.2, hw.1, ?_⟩
        rw [proc_stop hq']; exact (h.upr _ q hw.1).2
      · split at hs
        · simp only [Option.some.injEq] at hs; subst hs
          change w.alive p = false at hdead; rw [hg.1] at hdead; cases hdead
        · simp at hs
  · have h := wdinv_of_reachable hr
    simp only [cstep, rok] at hs
    split at hs
    · rename_i s _
      simp only [cwhen] at hs; split at hs <;> simp at hs; subst hs
      rename_i hg; simp only [Bool.and_eq_true, beq_iff_eq] at hg
      exact ⟨s, hg.1.1, hg.2, hg.1.2, (h.upr i s hg.1.2).2⟩
    · simp at hs

/-- p of swarm i runs and the record isn't a running watchd's: p's takeover or its loop is enabled -/
theorem own_enabled {c : CCfg} {w : World} {i p : Nat} (hp : w.isOf i p) (ha : w.alive p = true)
    (hd : watchdUp w i = false) : (cstep c w (.takeover p)).isSome = true ∨ (cstep c w (.loop p)).isSome = true := by
  cases ht : (w.proc p).took
  · left; simp [cstep, takeover, cwhen, ha, ht]
  · right
    simp only [cstep, loop, ha, ht, Bool.and_self, Bool.not_true, Bool.false_eq_true, ite_false, hp.2]
    cases e : w.wdOf i with
    | none => rfl
    | some q =>
      have hq : w.alive q = false := by simpa [watchdUp, e] using hd
      have hqp : q ≠ p := fun x => by subst x; rw [ha] at hq; cases hq
      simp only [hqp, hq, beq_iff_eq, ite_false, Bool.and_false, Bool.or_false, Bool.not_false, ite_true]
      split <;> rfl

/-- after p's takeover or loop step, p holds swarm i's record or has stopped -/
theorem own_after {c : CCfg} {w w' : World} {i p : Nat} (h : WdInv c w) (hp : w.isOf i p) {a : CAction}
    (ha : a = .takeover p ∨ a = .loop p) (hs : cstep c w a = some w') : w'.alive p = false ∨ w'.wdOf i = some p := by
  have hi : i < w.wd.length := h.wdLen ▸ hp.2 ▸ h.swLt p hp.1
  rcases ha with rfl | rfl
  · simp only [cstep, takeover, cwhen] at hs; split at hs <;> simp at hs; subst hs
    right; simp only [World.wdOf, hp.2]; rw [R.getD_set]; simp [hi]
  · simp only [cstep, loop] at hs
    split at hs; · simp at hs
    split at hs
    · simp only [Option.some.injEq] at hs; subst hs; exact .inl (alive_stop_self w p)
    · split at hs; · simp at hs
      split at hs
      · simp only [Option.some.injEq] at hs; subst hs; exact .inl (alive_stop_self w p)
      · split at hs
        · simp only [Option.some.injEq] at hs; subst hs
          right; rw [wdOf_set]; simp [hp.2, hi]
        · simp at hs

/-- R1 (c): on a run fair to the ticks and to the watchd processes, a watchd that keeps running gets its swarm ticked at
infinitely many steps: the record's watchd, if it runs, ticks; if it doesn't, the one that runs takes the record over
(its start) or back (its loop). With or without `waitUp`: the old CLI's handover breaks (b), not this -/
theorem R1c_of {c : CCfg} (r : CRun c) (hf : r.Fair) (hw : r.FairWd) (h0 : CReachable c (r.st 0)) {i p n : Nat}
    (hi : (r.st n).isOf i p) (hp : ∀ m ≥ n, (r.st m).alive p = true) : ∀ N, ∃ m ≥ N, r.act m = .tick i := by
  intro N
  refine Classical.byContradiction fun hno => ?_
  have hno' : ∀ m ≥ N, r.act m ≠ .tick i := fun m hm e => hno ⟨m, hm, e⟩
  have hdown : ∃ N1, ∀ m ≥ N1, watchdUp (r.st m) i = false := by
    refine Classical.byContradiction fun hd => ?_
    have hup : ∀ N1, ∃ m ≥ N1, watchdUp (r.st m) i = true := fun N1 =>
      Classical.byContradiction fun hx => hd ⟨N1, fun m hm => by
        cases e : watchdUp (r.st m) i
        · rfl
        · exact absurd ⟨m, hm, e⟩ hx⟩
    obtain ⟨m, hm, ha⟩ := hf i hup N
    exact hno' m hm ha
  obtain ⟨N1, hN1⟩ := hdown
  have hen : ∀ m ≥ max n N1,
      (cstep c (r.st m) (.takeover p)).isSome = true ∨ (cstep c (r.st m) (.loop p)).isSome = true := fun m hm =>
    own_enabled (r.isOf hi m (by omega)) (hp m (by omega)) (hN1 m (by omega))
  have hio : ∀ a, (a = CAction.takeover p ∨ a = .loop p) → (∀ K, ∃ m ≥ K, (cstep c (r.st m) a).isSome = true) → False := by
    intro a ha hinf
    obtain ⟨m, hm, e⟩ := hw a ⟨p, ha⟩ hinf (max n N1)
    have hs := r.ok m; rw [e] at hs
    rcases own_after (wdinv_of_reachable (r.reachable h0 m)) (r.isOf hi m (by omega)) ha hs with hd | hr
    · rw [hp (m + 1) (by omega)] at hd; cases hd
    · have := hN1 (m + 1) (by omega); simp [watchdUp, hr, hp (m + 1) (by omega)] at this
  refine hio (.takeover p) (.inl rfl) fun K => Classical.byContradiction fun hk => hio (.loop p) (.inr rfl) fun K' => ?_
  rcases hen (max (max n N1) (max K K')) (by omega) with e | e
  · exact absurd ⟨_, by omega, e⟩ hk
  · exact ⟨_, by omega, e⟩

/-- R1 (c) for a restart: the watchd `--restart` starts at step n, if it keeps running, gets its swarm ticked at
infinitely many steps -/
theorem restart_ticks {c : CCfg} (r : CRun c) (hf : r.Fair) (hw : r.FairWd) (h0 : CReachable c (r.st 0)) {i x n : Nat}
    (hr : r.act n = .restart i x) (hp : ∀ m ≥ n + 1, (r.st m).alive (r.st n).wds.length = true) :
    ∀ N, ∃ m ≥ N, r.act m = .tick i := by
  refine R1c_of r hf hw h0 (n := n + 1) ?_ hp
  have hs := r.ok n; rw [hr] at hs
  simp only [cstep, restart, cwhen] at hs; split at hs <;> simp at hs
  rw [← hs]
  exact ⟨by simp, by simp only [World.proc]; rw [R.getD_append_one]; simp⟩

end Swarm

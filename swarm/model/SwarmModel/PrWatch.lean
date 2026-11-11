import SwarmModel.Model

/-! PRs and the wait on their checks (board #28). The main model has no PRs, no CI and no `swarm stay`; this layer has
the least that states the stall: tasks claimed by agents, each task's PR (opened, its head's checks pending, green or
red, merged or not), agents working or idle with their waiter armed, staying or not, with an urgent message unread or
not, and watchd's poll of the PRs (`ci.pr_watch`). Time and leases are left out: in the main model an idle owner's
lapsed claim is reaped (L2), which is how the stall ended without the fix, two hours on, the task reopened with its PR
green or merged.

Without the fix nothing told an agent its PR's checks had finished: watchd polls the base's push runs, not PR checks,
and agents are told not to poll `gh`. The fix (`wakeFix`, `closeFix`): watchd polls the PRs from live owners' task
branches; in a repo whose `ci.flow` is pr-gated (`gated`) a finished verdict wakes the owner, once per head; in every
flow a merged PR closes its task. P1 (the woken stayer, pr-gated) and P2 (no merged task stays claimed) are stated over
fair runs, refuted with each switch off by the stalls of Findings.lean (#30, #31) and proved with it on (`P1_of`,
`P2_of`). `pollTask` is the model's decision; `Decide.prActL` is the Lua's, lifted (`Decide.prAct_lifted`). -/

namespace Swarm.PrW
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

inductive Checks where | pending | green | red
  deriving DecidableEq, Repr, Inhabited

/-- ci.verdict's name for it -/
def Checks.name : Checks → String | .pending => "pending" | .green => "green" | .red => "red"

/-- the instance: sizes, the repo's CI flow, and the fixes' switches. The defaults are main now -/
structure PCfg where
  nagents : Nat := 1
  ntasks : Nat := 1
  /-- `.claude/swarm.json` `ci.flow` is "pr-gated": a PR's checks gate its merge -/
  gated : Bool := false
  /-- board #28: in a pr-gated repo watchd's poll wakes the owner when its PR's checks finish -/
  wakeFix : Bool := true
  /-- board #28: watchd's poll marks a claimed task done when its PR is merged, in any flow -/
  closeFix : Bool := true
  deriving DecidableEq, Repr, Inhabited

/-- a task's PR, from the task's branch into its base; `told`: watchd told the owner of this head's verdict (its
`pr-wake` event) -/
structure Pr where
  opened : Bool := false
  checks : Checks := .pending
  merged : Bool := false
  told : Bool := false
  deriving DecidableEq, Repr, Inhabited

inductive PSt where | opn | claimed | done
  deriving DecidableEq, Repr, Inhabited

structure PTask where
  st : PSt := .opn
  owner : Nat := 0
  pr : Pr := {}
  deriving DecidableEq, Repr, Inhabited

structure PAgent where
  /-- else idle, its waiter armed -/
  working : Bool := true
  /-- `swarm stay` -/
  stays : Bool := false
  /-- an urgent message to it is unread: its waiter wakes it on that (msgs.wakes) -/
  urgent : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- tasks and agents by index from 0 -/
structure PWorld where
  task : List PTask
  ag : List PAgent
  deriving DecidableEq, Repr, Inhabited

def PWorld.tk (w : PWorld) (t : Nat) : PTask := w.task.getD t default
def PWorld.agt (w : PWorld) (a : Nat) : PAgent := w.ag.getD a default
def PWorld.setTk (w : PWorld) (t : Nat) (f : PTask → PTask) : PWorld := { w with task := w.task.modify t f }
def PWorld.setAg (w : PWorld) (a : Nat) (f : PAgent → PAgent) : PWorld := { w with ag := w.ag.modify a f }

def pinit (c : PCfg) : PWorld := { task := List.replicate c.ntasks {}, ag := List.replicate c.nagents {} }

def pwhen (b : Bool) (w : PWorld) : Option PWorld := if b then some w else none

/-- a runs a command: working, its inbox read (the hooks deliver before each tool) -/
def ready (w : PWorld) (a : Nat) : Bool := (w.agt a).working && !(w.agt a).urgent
def mine (w : PWorld) (a t : Nat) : Bool := (w.tk t).st == .claimed && (w.tk t).owner == a

/-- watchd's poll of one task, the model's decision: a claimed task whose PR merged is done (`closeFix`); in a pr-gated
repo one whose PR's checks finished, its owner not yet told, is told (`wakeFix`) -/
def pollTask (c : PCfg) (k : PTask) : PTask :=
  if k.st == .claimed && k.pr.opened && k.pr.merged then (if c.closeFix then { k with st := .done } else k)
  else if k.st == .claimed && k.pr.opened && c.gated && c.wakeFix && k.pr.checks != .pending && !k.pr.told then
    { k with pr := { k.pr with told := true } }
  else k

/-- the poll posts to b: some task of b's changed (each change posts one urgent message to its owner) -/
def owed (c : PCfg) (w : PWorld) (b : Nat) : Bool := w.task.any fun k => k.owner == b && pollTask c k != k

/-- watchd's poll (ci.pr_watch): every task at once, an urgent message to each owner told -/
def poll (c : PCfg) (w : PWorld) : PWorld :=
  { task := w.task.map (pollTask c), ag := w.ag.mapIdx fun b g => if owed c w b then { g with urgent := true } else g }

inductive PAction where
  | claim (a t : Nat)
  /-- `gh pr create` from the task's branch -/
  | openPr (a t : Nat)
  /-- a new head: its checks start again -/
  | push (a t : Nat)
  | stay (a : Nat) (v : Bool)
  /-- the Stop hook: idle, its waiter armed -/
  | stop (a : Nat)
  | read (a : Nat)
  /-- `gh pr merge`; in a pr-gated repo only once the checks are green -/
  | merge (a t : Nat)
  | done (a t : Nat)
  /-- CI: the head's checks finish -/
  | finish (t : Nat) (ok : Bool)
  /-- watchd's tick (`swarm watchd --ci`): with the switches off it does nothing to PRs -/
  | poll
  /-- the waiter wakes the agent on an urgent message -/
  | wake (a : Nat)
  deriving DecidableEq, Repr

def pstep (c : PCfg) (w : PWorld) : PAction → Option PWorld
  | .claim a t => pwhen (a < c.nagents && t < c.ntasks && ready w a && (w.tk t).st == .opn)
      (w.setTk t fun _ => { st := .claimed, owner := a })
  | .openPr a t => pwhen (ready w a && mine w a t && !(w.tk t).pr.opened) (w.setTk t fun k => { k with pr := { opened := true } })
  | .push a t => pwhen (ready w a && mine w a t && (w.tk t).pr.opened && !(w.tk t).pr.merged)
      (w.setTk t fun k => { k with pr := { k.pr with checks := .pending, told := false } })
  | .stay a v => pwhen (ready w a && (w.agt a).stays != v) (w.setAg a ({ · with stays := v }))
  | .stop a => pwhen (ready w a) (w.setAg a ({ · with working := false }))
  | .read a => pwhen ((w.agt a).working && (w.agt a).urgent) (w.setAg a ({ · with urgent := false }))
  | .merge a t => pwhen (ready w a && mine w a t && (w.tk t).pr.opened && !(w.tk t).pr.merged
        && (!c.gated || (w.tk t).pr.checks == .green))
      (w.setTk t fun k => { k with pr := { k.pr with merged := true } })
  | .done a t => pwhen (ready w a && mine w a t) (w.setTk t ({ · with st := .done }))
  | .finish t ok => pwhen ((w.tk t).pr.opened && (w.tk t).pr.checks == .pending && !(w.tk t).pr.merged)
      (w.setTk t fun k => { k with pr := { k.pr with checks := if ok then .green else .red } })
  | .poll => some (poll c w)
  | .wake a => pwhen (!(w.agt a).working && (w.agt a).urgent) (w.setAg a ({ · with working := true, urgent := false }))

inductive PReachable (c : PCfg) : PWorld → Prop
  | init : PReachable c (pinit c)
  | step {w w' : PWorld} (act : PAction) : PReachable c w → pstep c w act = some w' → PReachable c w'

def prun (c : PCfg) (acts : List PAction) : Option PWorld := acts.foldlM (pstep c) (pinit c)

theorem preachable_of_run {c : PCfg} {acts : List PAction} {w : PWorld} (h : prun c acts = some w) : PReachable c w := by
  suffices ∀ (acts : List PAction) (w0 w : PWorld), PReachable c w0 → acts.foldlM (pstep c) w0 = some w → PReachable c w from
    this acts _ w .init h
  intro acts
  induction acts with
  | nil => intro w0 w h0 h; simp [List.foldlM] at h; exact h ▸ h0
  | cons x xs ih =>
    intro w0 w h0 h
    simp only [List.foldlM_cons, Option.bind_eq_bind] at h
    cases h1 : pstep c w0 x with
    | none => simp [h1] at h
    | some w1 => rw [h1] at h; exact ih w1 w (.step x h0 h1) h

structure PRun (c : PCfg) where
  st : Nat → PWorld
  act : Nat → PAction
  ok : ∀ n, pstep c (st n) (act n) = some (st (n + 1))

/-- what fairness makes happen if it stays enabled: watchd polls, a waiter with an urgent message wakes, a working agent
reads its messages, CI finishes -/
def pfair (w : PWorld) : List PAction :=
  .poll :: (List.range w.ag.length).flatMap (fun a => [.wake a, .read a])
    ++ (List.range w.task.length).flatMap fun t => [.finish t true, .finish t false]

def PRun.Fair {c : PCfg} (r : PRun c) : Prop :=
  ∀ f, (∀ N, ∃ n ≥ N, f ∈ pfair (r.st n) ∧ (pstep c (r.st n) f).isSome) → ∀ N, ∃ n ≥ N, r.act n = f

/-- a stays idle for its PR's checks: it owns claimed t and stays, idle; t's PR is open and green, and watchd has not
told it so -/
def waitsGreen (w : PWorld) (a t : Nat) : Bool :=
  let k := w.tk t
  mine w a t && !(w.agt a).working && (w.agt a).stays && k.pr.opened && k.pr.checks == .green && !k.pr.merged && !k.pr.told

/-- t is claimed though its PR is merged -/
def mergedClaimed (w : PWorld) (t : Nat) : Bool := (w.tk t).st == .claimed && (w.tk t).pr.merged

/-- P1 (pr-gated): on a fair run from a reachable state, an agent that stays idle for its PR's checks once they are green
is woken -/
def P1 (c : PCfg) : Prop := ∀ r : PRun c, r.Fair → PReachable c (r.st 0) →
  ∀ n a t, waitsGreen (r.st n) a t = true → ∃ m ≥ n, ((r.st m).agt a).working = true
/-- P2 (every flow): on a fair run from a reachable state, a task whose PR is merged does not stay claimed forever -/
def P2 (c : PCfg) : Prop := ∀ r : PRun c, r.Fair → PReachable c (r.st 0) →
  ∀ n t, mergedClaimed (r.st n) t = true → ∃ m ≥ n, ((r.st m).tk t).st ≠ .claimed

-- ---------- the stalls: a run that stays in one state, watchd's poll its only step ----------

/-- after `pre`, x leaves the world as it is, every fair action enabled there is x, and `p` holds -/
def stall (c : PCfg) (pre : List PAction) (x : PAction) (p : PWorld → Bool) : Bool :=
  (prun c pre).any fun w => pstep c w x == some w && p w && (pfair w).all fun f => (pstep c w f).isNone || f == x

theorem fair_of_stall {c : PCfg} {pre : List PAction} {x : PAction} {p : PWorld → Bool} (h : stall c pre x p = true) :
    ∃ r : PRun c, r.Fair ∧ PReachable c (r.st 0) ∧ ∀ n, p (r.st n) = true := by
  unfold stall at h
  cases e : prun c pre with
  | none => simp [e] at h
  | some w =>
    simp only [e, Option.any_some, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true,
      Option.isNone_iff_eq_none] at h
    obtain ⟨⟨hx, hp⟩, hf⟩ := h
    refine ⟨⟨fun _ => w, fun _ => x, fun _ => hx⟩, ?_, preachable_of_run e, fun _ => hp⟩
    intro f hen N
    obtain ⟨n, -, hm, hs⟩ := hen 0
    rcases hf f hm with h0 | h0
    · simp [h0] at hs
    · exact ⟨N, Nat.le_refl _, h0.symm⟩

theorem not_P1_of {c : PCfg} {pre : List PAction} {x : PAction} {a t : Nat}
    (h : stall c pre x fun w => waitsGreen w a t) : ¬ P1 c := by
  intro hp
  obtain ⟨r, hf, h0, hw⟩ := fair_of_stall h
  obtain ⟨m, -, hm⟩ := hp r hf h0 0 a t (hw 0)
  have := hw m
  simp only [waitsGreen, Bool.and_eq_true, Bool.not_eq_true'] at this
  rw [this.1.1.1.1.1.2] at hm; cases hm

theorem not_P2_of {c : PCfg} {pre : List PAction} {x : PAction} {t : Nat}
    (h : stall c pre x fun w => mergedClaimed w t) : ¬ P2 c := by
  intro hp
  obtain ⟨r, hf, h0, hw⟩ := fair_of_stall h
  obtain ⟨m, -, hm⟩ := hp r hf h0 0 t (hw 0)
  have := hw m
  simp only [mergedClaimed, Bool.and_eq_true, beq_iff_eq] at this
  exact hm this.1

-- ---------- lists ----------

theorem getD_modify {α} (l : List α) (i j : Nat) (f : α → α) (d : α) :
    (l.modify i f).getD j d = if i = j ∧ j < l.length then f (l.getD j d) else l.getD j d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_modify]
  by_cases h : j < l.length
  · simp only [List.getElem?_eq_getElem h, Option.map_some, Option.getD_some]
    by_cases e : i = j <;> simp [e, h]
  · simp [List.getElem?_eq_none (Nat.le_of_not_lt h), h]

theorem getD_map_def {α} (l : List α) (j : Nat) (f : α → α) (d : α) (hd : f d = d) :
    (l.map f).getD j d = f (l.getD j d) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[j]? <;> simp [hd]

theorem getD_mapIdx {α} (l : List α) (j : Nat) (g : Nat → α → α) (d : α) :
    (l.mapIdx g).getD j d = if j < l.length then g j (l.getD j d) else d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_mapIdx]
  by_cases h : j < l.length
  · simp [List.getElem?_eq_getElem h, h]
  · simp [List.getElem?_eq_none (Nat.le_of_not_lt h), h]

@[simp] theorem setTk_agt (w : PWorld) (t : Nat) (f : PTask → PTask) (b : Nat) : (w.setTk t f).agt b = w.agt b := rfl
@[simp] theorem setAg_tk (w : PWorld) (a : Nat) (f : PAgent → PAgent) (u : Nat) : (w.setAg a f).tk u = w.tk u := rfl
@[simp] theorem setAg_ag_length (w : PWorld) (a : Nat) (f : PAgent → PAgent) : (w.setAg a f).ag.length = w.ag.length := by
  simp [PWorld.setAg]
@[simp] theorem setTk_ag_length (w : PWorld) (t : Nat) (f : PTask → PTask) : (w.setTk t f).ag.length = w.ag.length := rfl
theorem tk_setTk (w : PWorld) (t u : Nat) (f : PTask → PTask) :
    (w.setTk t f).tk u = if t = u ∧ u < w.task.length then f (w.tk u) else w.tk u := getD_modify ..
theorem agt_setAg (w : PWorld) (a b : Nat) (f : PAgent → PAgent) :
    (w.setAg a f).agt b = if a = b ∧ b < w.ag.length then f (w.agt b) else w.agt b := getD_modify ..
theorem tk_setTk_ne (w : PWorld) {t u : Nat} (f : PTask → PTask) (h : t ≠ u) : (w.setTk t f).tk u = w.tk u := by
  rw [tk_setTk]; simp [h]
theorem agt_setAg_ne (w : PWorld) {a b : Nat} (f : PAgent → PAgent) (h : a ≠ b) : (w.setAg a f).agt b = w.agt b := by
  rw [agt_setAg]; simp [h]

theorem pollTask_default (c : PCfg) : pollTask c default = default := by
  simp [pollTask, default, instInhabitedPTask]
  rfl

theorem poll_tk (c : PCfg) (w : PWorld) (u : Nat) : (poll c w).tk u = pollTask c (w.tk u) :=
  getD_map_def _ _ _ _ (pollTask_default c)

theorem poll_agt (c : PCfg) (w : PWorld) (b : Nat) : (poll c w).agt b =
    if b < w.ag.length then (if owed c w b then { w.agt b with urgent := true } else w.agt b) else default := by
  show (w.ag.mapIdx _).getD b default = _
  rw [getD_mapIdx]; rfl

@[simp] theorem poll_ag_length (c : PCfg) (w : PWorld) : (poll c w).ag.length = w.ag.length := by simp [poll]

/-- an agent out of range reads as working: an idle one is in range -/
theorem idle_lt {w : PWorld} {a : Nat} (h : (w.agt a).working = false) : a < w.ag.length := by
  apply Classical.byContradiction; intro hn
  have : w.agt a = default := by simp [PWorld.agt, List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hn)]
  rw [this] at h; cases h

/-- a claimed task is in range -/
theorem claimed_lt {w : PWorld} {t : Nat} (h : (w.tk t).st = .claimed) : t < w.task.length := by
  apply Classical.byContradiction; intro hn
  have : w.tk t = default := by simp [PWorld.tk, List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hn)]
  rw [this] at h; cases h

theorem owed_of {c : PCfg} {w : PWorld} {t : Nat} (ht : t < w.task.length) (h : pollTask c (w.tk t) ≠ w.tk t) :
    owed c w (w.tk t).owner = true := by
  simp only [owed, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
  exact ⟨w.tk t, by simp [PWorld.tk, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht], rfl, h⟩

-- ---------- P1 ----------

/-- an urgent message to idle agent a is unread -/
def urgentIdle (w : PWorld) (a : Nat) : Bool := (w.agt a).urgent && !(w.agt a).working

/-- a step that leaves a idle keeps an urgent message to it unread -/
theorem urgent_keep {c : PCfg} {w w' : PWorld} {a : Nat} {act : PAction} (hs : pstep c w act = some w')
    (hu : urgentIdle w a = true) (hw : (w'.agt a).working = false) : urgentIdle w' a = true := by
  simp only [urgentIdle, Bool.and_eq_true, Bool.not_eq_true'] at hu ⊢
  refine ⟨?_, hw⟩
  have hl := idle_lt hw
  cases act with
  | claim b u | openPr b u | push b u | merge b u | done b u | finish b u =>
    simp only [pstep, pwhen, Option.ite_none_right_eq_some, Option.some.injEq] at hs
    obtain ⟨-, rfl⟩ := hs; simpa using hu.1
  | stay b v =>
    simp only [pstep, pwhen, Option.ite_none_right_eq_some, Option.some.injEq] at hs
    obtain ⟨-, rfl⟩ := hs; rw [agt_setAg]; split <;> simp [hu.1]
  | stop b =>
    simp only [pstep, pwhen, Option.ite_none_right_eq_some, Option.some.injEq] at hs
    obtain ⟨-, rfl⟩ := hs; rw [agt_setAg]; split <;> simp [hu.1]
  | read b =>
    simp only [pstep, pwhen, Option.ite_none_right_eq_some, Option.some.injEq] at hs
    obtain ⟨hg, rfl⟩ := hs
    have hb : b ≠ a := by rintro rfl; simp [hu.2] at hg
    rw [agt_setAg_ne _ _ hb]; exact hu.1
  | poll =>
    simp only [pstep, Option.some.injEq] at hs
    subst hs; simp only [poll_ag_length] at hl
    rw [poll_agt]; simp only [hl, ite_true]; split <;> simp [hu.1]
  | wake b =>
    simp only [pstep, pwhen, Option.ite_none_right_eq_some, Option.some.injEq] at hs
    obtain ⟨-, rfl⟩ := hs
    by_cases e : b = a
    · subst e; simp only [setAg_ag_length] at hl; simp [agt_setAg, hl] at hw
    · rw [agt_setAg_ne _ _ e]; exact hu.1

/-- a step that leaves a idle keeps it waiting on green checks, or leaves an urgent message to it unread -/
theorem wait_keep {c : PCfg} {w w' : PWorld} {a t : Nat} {act : PAction} (hs : pstep c w act = some w')
    (hg : waitsGreen w a t = true) (hw : (w'.agt a).working = false) :
    waitsGreen w' a t = true ∨ urgentIdle w' a = true := by
  simp only [waitsGreen, mine, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hg
  obtain ⟨⟨⟨⟨⟨⟨⟨hc, ho⟩, hi⟩, hst⟩, hop⟩, hgr⟩, hm⟩, htold⟩ := hg
  have hlt := claimed_lt hc
  -- the task and the agent as they were: still waiting
  have same : ∀ w' : PWorld, w'.tk t = w.tk t → (w'.agt a).working = false → (w'.agt a).stays = true →
      waitsGreen w' a t = true := fun w' e1 e2 e3 => by
    simp [waitsGreen, mine, e1, e2, e3, hc, ho, hop, hgr, hm, htold]
  -- an owner's command on its task: a is idle, so the owner is another agent and the task another
  have cmd : ∀ (b u : Nat) (f : PTask → PTask), ready w b = true → mine w b u = true →
      waitsGreen (w.setTk u f) a t = true := by
    intro b u f hr hmi
    have hb : b ≠ a := by rintro rfl; simp [ready, hi] at hr
    have hu : u ≠ t := by rintro rfl; simp [mine, ho, Ne.symm hb] at hmi
    exact same _ (tk_setTk_ne _ _ hu) (by simpa using hi) (by simpa using hst)
  -- another agent's own change
  have other : ∀ (b : Nat) (f : PAgent → PAgent), b ≠ a → waitsGreen (w.setAg b f) a t = true := fun b f hb =>
    same _ (by simp) (by rw [agt_setAg_ne _ _ hb]; exact hi) (by rw [agt_setAg_ne _ _ hb]; exact hst)
  cases act with
  | claim b u =>
    simp only [pstep, pwhen, Option.ite_none_right_eq_some, Option.some.injEq] at hs
    obtain ⟨hg, rfl⟩ := hs
    have hu : u ≠ t := by rintro rfl; simp [hc] at hg
    exact .inl (same _ (tk_setTk_ne _ _ hu) (by simpa using hi) (by simpa using hst))
  | openPr b u =>
    simp only [pstep, pwhen, Option.ite_none_right_eq_some, Option.some.injEq, Bool.and_eq_true] at hs
    obtain ⟨⟨⟨h1, h2⟩, -⟩, rfl⟩ := hs; exact .inl (cmd b u _ h1 h2)
  | push b u =>
    simp only [pstep, pwhen, Option.ite_none_right_eq_some, Option.some.injEq, Bool.and_eq_true] at hs
    obtain ⟨⟨⟨⟨h1, h2⟩, -⟩, -⟩, rfl⟩ := hs; exact .inl (cmd b u _ h1 h2)
  | done b u =>
    simp only [pstep, pwhen, Option.ite_none_right_eq_some, Option.some.injEq, Bool.and_eq_true] at hs
    obtain ⟨⟨h1, h2⟩, rfl⟩ := hs; exact .inl (cmd b u _ h1 h2)
  | merge b u =>
    simp only [pstep, pwhen, Option.ite_none_right_eq_some, Option.some.injEq, Bool.and_eq_true] at hs
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, -⟩, -⟩, -⟩, rfl⟩ := hs; exact .inl (cmd b u _ h1 h2)
  | stay b v | stop b =>
    simp only [pstep, pwhen, Option.ite_none_right_eq_some, Option.some.injEq, Bool.and_eq_true] at hs
    obtain ⟨hg, rfl⟩ := hs
    have hb : b ≠ a := by rintro rfl; simp_all [ready]
    exact .inl (other b _ hb)
  | read b =>
    simp only [pstep, pwhen, Option.ite_none_right_eq_some, Option.some.injEq, Bool.and_eq_true] at hs
    obtain ⟨hg, rfl⟩ := hs
    have hb : b ≠ a := by rintro rfl; simp_all
    exact .inl (other b _ hb)
  | wake b =>
    simp only [pstep, pwhen, Option.ite_none_right_eq_some, Option.some.injEq, Bool.and_eq_true] at hs
    obtain ⟨-, rfl⟩ := hs
    have hb : b ≠ a := by rintro rfl; simp [agt_setAg, idle_lt hi] at hw
    exact .inl (other b _ hb)
  | finish u ok =>
    simp only [pstep, pwhen, Option.ite_none_right_eq_some, Option.some.injEq] at hs
    obtain ⟨hg, rfl⟩ := hs
    have hu : u ≠ t := by rintro rfl; simp [hgr] at hg
    exact .inl (same _ (tk_setTk_ne _ _ hu) (by simpa using hi) (by simpa using hst))
  | poll =>
    simp only [pstep, Option.some.injEq] at hs
    subst hs
    have hl := idle_lt hw; simp only [poll_ag_length] at hl
    by_cases hp : pollTask c (w.tk t) = w.tk t
    · refine .inl (same _ (by rw [poll_tk, hp]) hw ?_)
      rw [poll_agt]; simp only [hl, ite_true]; split <;> simp [hst]
    · right
      have := owed_of hlt hp; rw [ho] at this
      simp only [urgentIdle, Bool.and_eq_true, Bool.not_eq_true']
      refine ⟨?_, hw⟩
      rw [poll_agt]; simp [hl, this]

/-- with the fix in a pr-gated repo, the poll tells an agent waiting on green checks: an urgent message to it -/
theorem poll_tells {c : PCfg} (hg : c.gated = true) (hf : c.wakeFix = true) {w : PWorld} {a t : Nat}
    (h : waitsGreen w a t = true) : urgentIdle (poll c w) a = true := by
  simp only [waitsGreen, mine, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hc, ho⟩, hi⟩, -⟩, hop⟩, hgr⟩, hm⟩, htold⟩ := h
  have hp : pollTask c (w.tk t) ≠ w.tk t := by
    intro e
    have : (pollTask c (w.tk t)).pr.told = true := by simp [pollTask, hc, hop, hm, hg, hf, hgr, htold]
    rw [e, htold] at this; cases this
  have := owed_of (claimed_lt hc) hp; rw [ho] at this
  simp [urgentIdle, poll_agt, idle_lt hi, this, hi]

theorem Run.always {c : PCfg} {r : PRun c} {P : Nat → Prop} {n : Nat} (h0 : P n) (hs : ∀ k ≥ n, P k → P (k + 1)) :
    ∀ k ≥ n, P k := by
  intro k hk
  induction k with
  | zero => have : n = 0 := by omega
            subst this; exact h0
  | succ k ih =>
    by_cases e : n = k + 1
    · subst e; exact h0
    · exact hs k (by omega) (ih (by omega))

/-- P1 with the fix in a pr-gated repo -/
theorem P1_of (c : PCfg) (hg : c.gated = true) (hf : c.wakeFix = true) : P1 c := by
  intro r hfair _ n a t h0
  apply Classical.byContradiction
  intro hno
  have idle : ∀ k ≥ n, ((r.st k).agt a).working = false := fun k hk => by
    cases e : ((r.st k).agt a).working
    · rfl
    · exact absurd ⟨k, hk, e⟩ hno
  -- once an urgent message is unread, the waiter's wake is enabled from there on, so it happens: a works
  have woken : ∀ k ≥ n, urgentIdle (r.st k) a = true → False := by
    intro k hk hu
    have keep : ∀ j ≥ k, urgentIdle (r.st j) a = true :=
      Run.always (r := r) hu fun j hj hj' => urgent_keep (r.ok j) hj' (idle (j + 1) (by omega))
    have en : ∀ N, ∃ j ≥ N, PAction.wake a ∈ pfair (r.st j) ∧ (pstep c (r.st j) (.wake a)).isSome := by
      intro N
      refine ⟨max N k, Nat.le_max_left .., ?_, ?_⟩
      · have := idle_lt (idle (max N k) (by omega))
        simp only [pfair, List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_range]
        exact .inl (.inr ⟨a, this, by simp⟩)
      · have := keep (max N k) (Nat.le_max_right ..)
        simp only [urgentIdle, Bool.and_eq_true, Bool.not_eq_true'] at this
        simp [pstep, pwhen, this.1, this.2]
    obtain ⟨j, hj, ha⟩ := hfair _ en k
    have := r.ok j
    rw [ha] at this
    have hu := keep j hj
    simp only [urgentIdle, Bool.and_eq_true, Bool.not_eq_true'] at hu
    simp only [pstep, pwhen, hu.1, hu.2, Bool.not_false, Bool.and_self, ite_true, Option.some.injEq] at this
    have hw := idle (j + 1) (by omega)
    rw [← this, agt_setAg] at hw
    simp [idle_lt hu.2] at hw
  -- else a waits on green checks from n on, and the poll, always enabled, tells it
  have wait : ∀ k ≥ n, waitsGreen (r.st k) a t = true := Run.always (r := r) h0 fun k hk hw =>
    (wait_keep (r.ok k) hw (idle (k + 1) (by omega))).elim id fun hu => (woken (k + 1) (by omega) hu).elim
  obtain ⟨k, hk, hp⟩ := hfair .poll (fun N => ⟨N, Nat.le_refl _, by simp [pfair], by simp [pstep]⟩) n
  have := r.ok k
  rw [hp] at this
  simp only [pstep, Option.some.injEq] at this
  exact woken (k + 1) (by omega) (this ▸ poll_tells hg hf (wait k hk))

-- ---------- P2 ----------

/-- with `closeFix` the poll ends a merged task's claim -/
theorem poll_closes {c : PCfg} (hf : c.closeFix = true) {w : PWorld} {t : Nat} (h : mergedClaimed w t = true)
    (hop : (w.tk t).pr.opened = true) : ((poll c w).tk t).st ≠ .claimed := by
  simp only [mergedClaimed, Bool.and_eq_true, beq_iff_eq] at h
  rw [poll_tk]; simp [pollTask, h.1, h.2, hop, hf]

/-- a merged PR was opened: merge is the only step that sets `merged`, on an opened PR, and push and finish keep it -/
def mergedOpen (w : PWorld) : Prop := ∀ t, (w.tk t).pr.merged = true → (w.tk t).pr.opened = true

theorem mergedOpen_step {c : PCfg} {w w' : PWorld} {act : PAction} (hs : pstep c w act = some w') (h : mergedOpen w) :
    mergedOpen w' := by
  intro u hu
  cases act with
  | claim b v | openPr b v | push b v | merge b v | done b v | finish v b =>
    simp only [pstep, pwhen, Option.ite_none_right_eq_some, Option.some.injEq, Bool.and_eq_true] at hs
    obtain ⟨hg, rfl⟩ := hs
    rw [tk_setTk] at hu ⊢
    by_cases e : v = u ∧ u < w.task.length
    · rw [if_pos e] at hu ⊢
      all_goals (obtain ⟨rfl, -⟩ := e; have := h v; simp_all)
    · rw [if_neg e] at hu ⊢; exact h u hu
  | stay b v | stop b | read b | wake b =>
    simp only [pstep, pwhen, Option.ite_none_right_eq_some, Option.some.injEq] at hs
    obtain ⟨-, rfl⟩ := hs
    simp only [setAg_tk] at hu ⊢; exact h u hu
  | poll =>
    simp only [pstep, Option.some.injEq] at hs
    subst hs; rw [poll_tk] at hu ⊢
    have := h u
    unfold pollTask at hu ⊢
    split <;> (try split) <;> simp_all

theorem mergedOpen_reach {c : PCfg} {w : PWorld} (h : PReachable c w) : mergedOpen w := by
  induction h with
  | init =>
    intro u hu
    simp [pinit, PWorld.tk, List.getD_eq_getElem?_getD, List.getElem?_replicate] at hu
    split at hu <;> simp_all <;> cases hu
  | step act _ hs ih => exact mergedOpen_step hs ih

/-- a step keeps a merged task merged -/
theorem merged_keep {c : PCfg} {w w' : PWorld} {act : PAction} {t : Nat} (hs : pstep c w act = some w')
    (hmo : mergedOpen w) (h : mergedClaimed w t = true) (h' : (w'.tk t).st = .claimed) : mergedClaimed w' t = true := by
  simp only [mergedClaimed, Bool.and_eq_true, beq_iff_eq] at h ⊢
  refine ⟨h', ?_⟩
  have hop := hmo t h.2
  cases act with
  | claim b v | openPr b v | push b v | merge b v | done b v | finish v b =>
    simp only [pstep, pwhen, Option.ite_none_right_eq_some, Option.some.injEq, Bool.and_eq_true] at hs
    obtain ⟨hg, rfl⟩ := hs
    rw [tk_setTk] at h' ⊢
    split
    · rename_i e; obtain ⟨rfl, -⟩ := e; simp_all
    · exact h.2
  | stay b v | stop b | read b | wake b =>
    simp only [pstep, pwhen, Option.ite_none_right_eq_some, Option.some.injEq] at hs
    obtain ⟨-, rfl⟩ := hs
    simp only [setAg_tk]; exact h.2
  | poll =>
    simp only [pstep, Option.some.injEq] at hs
    subst hs; rw [poll_tk] at h' ⊢; unfold pollTask at h' ⊢; split <;> (try split) <;> simp_all

theorem preach_run {c : PCfg} {r : PRun c} (h0 : PReachable c (r.st 0)) : ∀ n, PReachable c (r.st n)
  | 0 => h0
  | n + 1 => .step _ (preach_run h0 n) (r.ok n)

/-- P2 with `closeFix` -/
theorem P2_of (c : PCfg) (hf : c.closeFix = true) : P2 c := by
  intro r hfair h0 n t hm
  apply Classical.byContradiction
  intro hno
  have cl : ∀ k ≥ n, ((r.st k).tk t).st = .claimed := fun k hk => by
    apply Classical.byContradiction; intro e; exact hno ⟨k, hk, e⟩
  have keep : ∀ k ≥ n, mergedClaimed (r.st k) t = true :=
    Run.always (r := r) hm fun k hk hk' =>
      merged_keep (r.ok k) (mergedOpen_reach (preach_run h0 k)) hk' (cl (k + 1) (by omega))
  obtain ⟨k, hk, hp⟩ := hfair .poll (fun N => ⟨N, Nat.le_refl _, by simp [pfair], by simp [pstep]⟩) n
  have := r.ok k
  rw [hp] at this
  simp only [pstep, Option.some.injEq] at this
  have hmk := keep k hk
  have hop := mergedOpen_reach (preach_run h0 k) t (by
    simp only [mergedClaimed, Bool.and_eq_true] at hmk; exact hmk.2)
  exact poll_closes hf hmk hop (this ▸ cl (k + 1) (by omega))

/-- P1 and P2 hold of a pr-gated repo with the fix, as main runs it; P2 of any flow -/
theorem main_P1 : P1 { gated := true } := P1_of _ rfl rfl
theorem main_P2 (c : PCfg) (hf : c.closeFix = true) : P2 c := P2_of c hf

end Swarm.PrW

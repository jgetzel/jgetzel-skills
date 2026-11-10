import SwarmModel.Liveness

/-! Fair runs, and L2 over them. A run is an infinite sequence of steps; it is fair when each action of `fair c`
that is enabled at infinitely many steps happens at infinitely many steps. -/

namespace Swarm
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.deprecated false

structure Run (c : Cfg) where
  st : Nat → State
  act : Nat → Action
  ok : ∀ n, step c (st n) (act n) = some (st (n + 1))

def Run.Fair {c : Cfg} (r : Run c) : Prop :=
  ∀ f, (∀ N, ∃ n ≥ N, f ∈ fair c (r.st n) ∧ (step c (r.st n) f).isSome) → ∀ N, ∃ n ≥ N, r.act n = f

theorem tk_setTask' {s : State} {t u : Nat} {f : Task → Task} (h : (s.tk u).st ≠ .absent) :
    (setTask s t f).tk u = if u = t then f (s.tk u) else s.tk u := by
  split
  · subst_vars; exact tk_setTask_self h
  · exact tk_setTask_ne ‹_›

theorem showMsg_agt (s : State) (a i b : Nat) : ∃ bl, (showMsg s a i).agt b = { s.agt b with believes := bl } := by
  unfold showMsg; simp only []
  split
  · exact ⟨_, rfl⟩
  · split
    · rw [agt_setAg]; split
      · exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
theorem showAll_agt (a : Nat) (ids : List Nat) (b : Nat) : ∀ s : State, ∃ bl, (showAll s a ids).agt b = { s.agt b with believes := bl } := by
  induction ids with
  | nil => intro s; exact ⟨_, rfl⟩
  | cons i is ih =>
    intro s
    obtain ⟨b1, e1⟩ := showMsg_agt s a i b
    obtain ⟨b2, e2⟩ := ih (showMsg s a i)
    refine ⟨b2, ?_⟩
    simp only [showAll, List.foldl_cons] at e2 ⊢
    rw [e2, e1]
theorem deliver_agt (s : State) (a b : Nat) : ∃ bl, (deliver s a).agt b = { s.agt b with believes := bl } := showAll_agt ..

@[simp] theorem tk_of_task {s s' : State} (h : s'.task = s.task) (t : Nat) : s'.tk t = s.tk t := by simp [State.tk, h]
@[simp] theorem agt_of_ag {s s' : State} (h : s'.ag = s.ag) (t : Nat) : s'.agt t = s.agt t := by simp [State.agt, h]
@[simp] theorem setAg_tk (s : State) (a : Nat) (f : Agent → Agent) (t : Nat) : (setAg s a f).tk t = s.tk t := tk_of_task (setAg_task ..) t
@[simp] theorem setTask_agt (s : State) (a : Nat) (f : Task → Task) (b : Nat) : (setTask s a f).agt b = s.agt b := agt_of_ag (setTask_ag ..) b
@[simp] theorem post_tk (s : State) (m : Msg) (t : Nat) : (post s m).tk t = s.tk t := tk_of_task (post_task ..) t
@[simp] theorem post_agt (s : State) (m : Msg) (t : Nat) : (post s m).agt t = s.agt t := agt_of_ag (post_ag ..) t
@[simp] theorem takes_tk (c : Cfg) (s : State) (a t u : Nat) : (takes c s a t).tk u = s.tk u := tk_of_task (takes_task ..) u
@[simp] theorem deliver_tk (s : State) (a u : Nat) : (deliver s a).tk u = s.tk u := tk_of_task (deliver_task ..) u
@[simp] theorem unbelieve_tk (s : State) (a t u : Nat) : (unbelieve s a t).tk u = s.tk u := tk_of_task (unbelieve_task ..) u
@[simp] theorem awake_tk (s : State) (a u : Nat) : (awake s a).tk u = s.tk u := tk_of_task (awake_task ..) u
@[simp] theorem claimed_agt (s : State) (a t b : Nat) : (claimed s a t).agt b = s.agt b := by
  unfold claimed; simp
theorem takes_agt (c : Cfg) (s : State) (a t b : Nat) : ∃ bl, (takes c s a t).agt b = { s.agt b with believes := bl } := by
  unfold takes; simp only []
  split <;> (simp only [State.agt]; exact (by have := agt_setAg s a b (fun g => { g with believes := t :: g.believes }); simp only [State.agt] at this; rw [this]; split <;> exact ⟨_, rfl⟩))

@[simp] theorem deliver_st (s : State) (a b : Nat) : ((deliver s a).agt b).st = (s.agt b).st := by
  obtain ⟨bl, e⟩ := deliver_agt s a b; rw [e]
@[simp] theorem deliver_boot (s : State) (a b : Nat) : ((deliver s a).agt b).boot = (s.agt b).boot := by
  obtain ⟨bl, e⟩ := deliver_agt s a b; rw [e]
@[simp] theorem takes_st (c : Cfg) (s : State) (a t b : Nat) : ((takes c s a t).agt b).st = (s.agt b).st := by
  obtain ⟨bl, e⟩ := takes_agt c s a t b; rw [e]
@[simp] theorem takes_boot (c : Cfg) (s : State) (a t b : Nat) : ((takes c s a t).agt b).boot = (s.agt b).boot := by
  obtain ⟨bl, e⟩ := takes_agt c s a t b; rw [e]
@[simp] theorem deliver_bg (s : State) (a b : Nat) : ((deliver s a).agt b).bg = (s.agt b).bg := by
  obtain ⟨bl, e⟩ := deliver_agt s a b; rw [e]
@[simp] theorem deliver_dead (s : State) (a b : Nat) : ((deliver s a).agt b).dead = (s.agt b).dead := by
  obtain ⟨bl, e⟩ := deliver_agt s a b; rw [e]
@[simp] theorem takes_bg (c : Cfg) (s : State) (a t b : Nat) : ((takes c s a t).agt b).bg = (s.agt b).bg := by
  obtain ⟨bl, e⟩ := takes_agt c s a t b; rw [e]
@[simp] theorem takes_dead (c : Cfg) (s : State) (a t b : Nat) : ((takes c s a t).agt b).dead = (s.agt b).dead := by
  obtain ⟨bl, e⟩ := takes_agt c s a t b; rw [e]
@[simp] theorem agt_mk (task ag lock log cursor start seen pend early git b) :
    (State.mk task ag lock log cursor start seen pend early git).agt b = ag.getD b default := rfl
@[simp] theorem tk_mk (task ag lock log cursor start seen pend early git t) :
    (State.mk task ag lock log cursor start seen pend early git).tk t = if t = 0 then default else task.getD (t - 1) default := rfl
@[simp] theorem agt_def (s : State) (b : Nat) : s.ag.getD b default = s.agt b := rfl
@[simp] theorem tk_def (s : State) (t : Nat) : (if t = 0 then default else s.task.getD (t - 1) default) = s.tk t := rfl

@[simp] theorem setAg_ag_length (s : State) (a : Nat) (f : Agent → Agent) : (setAg s a f).ag.length = s.ag.length := by
  simp [setAg]
theorem showAll_ag_length (a : Nat) (ids : List Nat) : ∀ s : State, (showAll s a ids).ag.length = s.ag.length := by
  induction ids with
  | nil => intro s; rfl
  | cons i is ih =>
    intro s; simp only [showAll, List.foldl_cons] at ih ⊢; rw [ih]
    unfold showMsg; simp only []; split <;> (try split) <;> first | rfl | simp [setAg]
@[simp] theorem deliver_ag_length (s : State) (a : Nat) : (deliver s a).ag.length = s.ag.length := showAll_ag_length ..

theorem endAgent_agt (s : State) (b a : Nat) : (endAgent s b).agt a =
    if b = a ∧ a < s.ag.length then { s.agt a with st := .ended, boot := false, believes := [] } else s.agt a := by
  unfold endAgent; rw [agt_of_ag (releaseAll_ag ..), agt_setAg]

theorem leaveIf_persist {s s' : State} {a t a₀ : Nat} {ok : Bool} (hs : leaveIf ok s a₀ = some s')
    (hst : (s.tk t).st = .claimed) (hown : (s.tk t).owner = some a) (hidle : (s.agt a).st = .idle)
    (hst' : (s'.tk t).st = .claimed) (hown' : (s'.tk t).owner = some a) (hidle' : (s'.agt a).st = .idle) :
    ((s.agt a).boot = true → (s'.agt a).boot = true) ∧ ((s.tk t).lease = false → (s'.tk t).lease = false) ∧
      ((s.agt a).bg = false → (s'.agt a).bg = false) ∧ ((s.agt a).dead = false → (s'.agt a).dead = false) := by
  simp only [leaveIf, when, Option.ite_none_right_eq_some, Option.some.injEq] at hs
  obtain ⟨hc, rfl⟩ := hs
  simp only [endAgent_agt, endAgent_tk, agt_setAg, setAg_tk, setAg_ag_length] at hidle' hst' hown' ⊢
  rcases Decidable.em (a = a₀) with hb | hb
  · subst hb
    by_cases hl : a < s.ag.length
    · simp_all
    · rw [agt_of_ge (Nat.le_of_not_lt hl)] at hidle; exact absurd hidle (by decide)
  · have hb' : ¬ a₀ = a := fun h => hb h.symm
    simp_all [held, hb, hb']

/-- Any action but the tick, between two states in which `a` idle holds `t`: a booting agent still boots, a lapsed
lease stays lapsed. -/
theorem persist {c : Cfg} {s s' : State} {a t : Nat} {act : Action} (hr : c.racy = false) (hn : act ≠ .tick)
    (hq : ∀ b, act ≠ .bgStart b ∧ act ≠ .die b)
    (hs : step c s act = some s') (h : idleClaim s a t = true) (h' : idleClaim s' a t = true) :
    ((s.agt a).boot = true → (s'.agt a).boot = true) ∧ ((s.tk t).lease = false → (s'.tk t).lease = false) ∧
      ((s.agt a).bg = false → (s'.agt a).bg = false) ∧ ((s.agt a).dead = false → (s'.agt a).dead = false) := by
  simp only [idleClaim, ownsClaimed, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h h'
  obtain ⟨⟨hst, hown⟩, hidle⟩ := h
  obtain ⟨⟨hst', hown'⟩, hidle'⟩ := h'

  cases act
  case leave a₀ => exact leaveIf_persist hs hst hown hidle hst' hown' hidle'
  case reapGone a₀ => exact leaveIf_persist hs hst hown hidle hst' hown' hidle'
  case bgStart => exact absurd rfl (hq _).1
  case die => exact absurd rfl (hq _).2
  case hcClear a₀ =>
    simp only [step, hcClear, when, Option.ite_none_right_eq_some, Option.some.injEq] at hs
    obtain ⟨hc, hs⟩ := hs
    have e1 : s'.tk t = s.tk t := by
      rw [← hs]; simp only [setAg_tk, deliver_tk]
      exact (tk_map (g := fun k => if (k.owner == some a₀ && k.st == TSt.blocked && k.hcq) = true then
        { k with st := .claimed, lease := true, hcq := false } else k) (by simp) rfl t).trans (by simp [hst])
    have hne : a ≠ a₀ := by rintro rfl; simp_all
    have e2 : ∃ bl, s'.agt a = { s.agt a with believes := bl } := by
      rw [← hs, agt_setAg, ite_eq_right_iff.2 (fun h => absurd h.1.symm hne)]; exact deliver_agt _ _ _
    obtain ⟨bl, e2⟩ := e2
    rw [e2]; exact ⟨id, fun h => by rw [e1]; exact h, id, id⟩
  case unblock t₀ =>
    simp only [step, unblock] at hs
    split at hs
    · simp only [when, Option.ite_none_right_eq_some, Option.some.injEq] at hs
      obtain ⟨hc, hs⟩ := hs
      have hne : t ≠ t₀ := by rintro rfl; simp_all
      have e1 : s'.tk t = s.tk t := by rw [← hs]; simp only [tk_mk, tk_def]; exact tk_setTask_ne hne
      have e2 : s'.agt a = s.agt a := by rw [← hs]; simp only [agt_mk, agt_def, post_ag, setTask_ag]
      rw [e1, e2]; exact ⟨id, id, id, id⟩
    · simp at hs
  all_goals (simp [step, claim, claimRead, claimWrite, renew, release, block, done, dropOwn, lock, unlock, postTo,
    readAll, stop, wake, wakeRead, wakeWrite, prompt, boot, waiterGone, age, cool, expire, expireLock,
    hcPrompt, add, after, drop, when, hr, bgEnd, gitCmd, world, stale, nudge] at hs hn)
  all_goals (try obtain ⟨hc, rfl⟩ := hs)
  all_goals (try obtain ⟨hc, hs⟩ := hs)
  all_goals (try subst hs)
  all_goals (try simp_all [claimed, awake, unbelieve, tk_setTask', agt_setAg, setAg_ag_length, working, busy, ownsClaimed, startable, held])
  all_goals (try ((repeat' split at *) <;> simp_all))
  all_goals (try (simp_all [State.agt, State.tk]; done))
  all_goals (try (simp only [agt_setAg, deliver_ag_length, deliver_boot, deliver_st, deliver_bg, deliver_dead] at *; (repeat' split at *) <;> simp_all; done))
  all_goals done

-- ---------- the tick ----------

/-- what a tick leaves of the pair (agent `a`, task `t`) in the states `y` after `z`: if `a` idle still holds `t`,
it is a fresh agent in the slot (booting), or both records are as in `z` -/
def Th (a t : Nat) (z y : State) : Prop :=
  ownsClaimed y a t = true ∧ (y.agt a).st = .idle →
    ((y.agt a).boot = true ∧ (y.agt a).bg = false ∧ (y.agt a).dead = false) ∨
      (y.tk t = z.tk t ∧ (y.agt a).boot = (z.agt a).boot ∧ (y.agt a).bg = (z.agt a).bg ∧ (y.agt a).dead = (z.agt a).dead)

theorem Th_end {a t b : Nat} {z y : State} (h : Th a t z y) : Th a t z (endAgent y b) := by
  rintro ⟨ho, hi⟩
  simp only [ownsClaimed, Bool.and_eq_true, beq_iff_eq] at ho
  rw [endAgent_tk] at ho
  rw [endAgent_agt] at hi
  rw [endAgent_tk, endAgent_agt]
  by_cases hb : held (y.tk t) b = true
  · simp [hb] at ho
  · by_cases hba : b = a ∧ a < y.ag.length
    · simp [hba] at hi
    · simp only [hb, hba, ite_false, Bool.false_eq_true] at ho hi ⊢
      exact h ⟨by simp [ownsClaimed, ho], hi⟩

theorem Th_told {a t b : Nat} {z y : State} {m : Msg} {f : Agent → Agent}
    (hf : ∀ g, (f g).st = g.st ∧ (f g).boot = g.boot ∧ (f g).bg = g.bg ∧ (f g).dead = g.dead) (h : Th a t z y) : Th a t z (post (setAg y b f) m) := by
  rintro ⟨ho, hi⟩
  simp only [post_agt, post_tk, setAg_tk, agt_setAg] at ho hi ⊢
  by_cases hba : b = a ∧ a < y.ag.length
  · rw [if_pos hba] at hi ⊢; rw [(hf _).1] at hi; rw [(hf _).2.1, (hf _).2.2.1, (hf _).2.2.2]; exact h ⟨ho, hi⟩
  · rw [if_neg hba] at hi ⊢; exact h ⟨ho, hi⟩

theorem claimed_tk (s : State) (a t u : Nat) : (claimed s a t).tk u = s.tk u ∨ ((claimed s a t).tk u).owner = some a := by
  unfold claimed
  exact (tk_setTask_or s t u _).elim Or.inl (fun e => Or.inr (by rw [e.2]))
theorem spawnFor_tk (c : Cfg) (pl : List Nat) (y : State) (t' u : Nat) :
    (spawnFor c pl y t').tk u = y.tk u ∨ ((spawnFor c pl y t').tk u).owner = nextAgent c y := by
  unfold spawnFor; split
  · rename_i a' hna
    split
    · simp only []
      rcases claimed_tk (State.mk _ _ _ _ _ _ _ _ _ _) a' t' u with e | e
      · exact Or.inl (by rw [e]; simp only [tk_mk, setAg_task, tk_def])
      · exact Or.inr (by rw [e, hna])
    · exact Or.inl rfl
  · exact Or.inl rfl

theorem spawnFor_agt (c : Cfg) (pl : List Nat) (y : State) (t' b : Nat) :
    (spawnFor c pl y t').agt b = y.agt b ∨
      (nextAgent c y = some b ∧ ((spawnFor c pl y t').agt b).st = .idle ∧ ((spawnFor c pl y t').agt b).boot = true ∧ ((spawnFor c pl y t').agt b).bg = false ∧ ((spawnFor c pl y t').agt b).dead = false) := by
  unfold spawnFor; split
  · rename_i a' hna
    split
    · simp only [claimed_agt, agt_mk, agt_def, agt_setAg]
      split
      · rename_i hh; obtain ⟨rfl, _⟩ := hh; exact Or.inr ⟨hna, rfl, rfl, rfl, rfl⟩
      · exact Or.inl rfl
    · exact Or.inl rfl
  · exact Or.inl rfl

theorem nextAgent_not_live {c : Cfg} {y : State} {a : Nat} (h : nextAgent c y = some a) : (y.agt a).live = false := by
  have := List.find?_some h
  simpa using this

theorem Th_spawn {c : Cfg} {a t t' : Nat} {pl : List Nat} {z y : State} (h : Th a t z y) :
    Th a t z (spawnFor c pl y t') := by
  rintro ⟨ho, hi⟩
  simp only [ownsClaimed, Bool.and_eq_true, beq_iff_eq] at ho
  rcases spawnFor_agt c pl y t' a with ha | ⟨hn, hs, hb, hbg, hdd⟩
  · rcases spawnFor_tk c pl y t' t with ht | ht
    · rw [ha] at hi ⊢; rw [ht] at ho ⊢
      exact h ⟨by simp [ownsClaimed, ho], hi⟩
    · exfalso
      have e : nextAgent c y = some a := by rw [← ht]; exact ho.2
      have := nextAgent_not_live e
      rw [ha] at hi; simp [Agent.live, hi] at this
  · exact Or.inl ⟨hb, hbg, hdd⟩

theorem lifecycle_Th {c : Cfg} {a t : Nat} {z : State} : Th a t z (lifecycle c z) := by
  have h0 : Th a t z z := fun _ => Or.inr ⟨rfl, rfl, rfl, rfl⟩
  unfold lifecycle; simp only []
  have h2 := foldl_inv (fun y b => if finished c z b && !reusable c z b then endAgent y b else y) (Th a t z) c.agents z h0
    (fun y b hy => by split; exact Th_end hy; exact hy)
  have h3 := foldl_inv (fun y b =>
    if reusable c z b && !(pool c z).all (y.agt b).told.contains then
      post (setAg y b fun g => { g with told := pool c z ++ g.told }) ⟨none, b, false, .digest, 0⟩
    else y) (Th a t z) c.agents _ h2 (fun y b hy => by split; exact Th_told (fun g => ⟨rfl, rfl, rfl, rfl⟩) hy; exact hy)
  split
  · exact h3
  · exact foldl_inv _ (Th a t z) _ _ h3 (fun y t' hy => Th_spawn hy)

theorem reapTask_ne {c : Cfg} {x : State} {t u : Nat} (h : (x.tk t).st ≠ .claimed) : ((reapTask c x u).tk t).st ≠ .claimed := by
  by_cases hu : u = t
  · subst hu; unfold reapTask; simp only []
    split
    · split
      · have : (x.tk u).st ≠ .absent := by intro e; simp [e] at *
        simp [tk_setTask_self this]
      · exact h
    · exact h
  · rw [reapTask_tk_ne (Ne.symm hu)]; exact h

theorem reapTask_fire {c : Cfg} {x : State} {t a : Nat} (hst : (x.tk t).st = .claimed) (ho : (x.tk t).owner = some a)
    (hl : (x.tk t).lease = false) (hk : keeps c (x.agt a) = false) : ((reapTask c x t).tk t).st ≠ .claimed := by
  unfold reapTask; simp only [ho, hst, hl, hk]
  have : (x.tk t).st ≠ .absent := by simp [hst]
  simp [tk_setTask_self this]

theorem reap_fold_ne {c : Cfg} {a t : Nat} : ∀ (l : List Nat) (x : State), t ∈ l →
    ((x.tk t).st ≠ .claimed ∨ ((x.tk t).st = .claimed ∧ (x.tk t).owner = some a ∧ (x.tk t).lease = false ∧ keeps c (x.agt a) = false)) →
    ((l.foldl (reapTask c) x).tk t).st ≠ .claimed
  | [], _, hm, _ => by cases hm
  | u :: us, x, hm, hq => by
    simp only [List.foldl_cons]
    by_cases hu : u = t
    · subst hu
      have h1 : ((reapTask c x u).tk u).st ≠ .claimed := by
        rcases hq with h | ⟨h1, h2, h3, h4⟩
        · exact reapTask_ne h
        · exact reapTask_fire h1 h2 h3 h4
      exact foldl_inv (reapTask c) (fun y : State => (y.tk u).st ≠ .claimed) us _ h1 (fun y v hy => reapTask_ne hy)
    · have hm' : t ∈ us := by
        rcases List.mem_cons.mp hm with e | e
        · exact absurd e.symm hu
        · exact e
      apply reap_fold_ne us _ hm'
      rw [reapTask_tk_ne (Ne.symm hu), State.agt, reapTask_ag]
      exact hq

theorem tick_persist {c : Cfg} {s s' : State} {a t : Nat} (hfix : c.release ≠ .ended) (ht : t ∈ c.tasks)
    (hbg : (s.agt a).bg = false) (hs : tick c s = some s') (h : idleClaim s a t = true) (h' : idleClaim s' a t = true) :
    ((s.agt a).boot = true → (s'.agt a).boot = true) ∧ ((s.tk t).lease = false → (s'.agt a).boot = true) ∧
      ((s.agt a).bg = false → (s'.agt a).bg = false) ∧ ((s.agt a).dead = false → (s'.agt a).dead = false) := by
  have e : s' = tickOf c s := by simp [tick, when] at hs; exact hs.2.symm
  subst e
  have hd : Th a t (reapLocks (reapTasks c s)) (tickOf c s) := lifecycle_Th
  have hz : (reapLocks (reapTasks c s)).agt a = s.agt a := by simp [State.agt]
  have hD := hd (by simpa [idleClaim] using h')
  rw [hz] at hD
  simp only [idleClaim, ownsClaimed, Bool.and_eq_true, beq_iff_eq] at h
  refine ⟨fun hb => ?_, fun hl => ?_, fun hb => ?_, fun hb => ?_⟩
  · rcases hD with hD | ⟨_, hD, _⟩
    · exact hD.1
    · rw [hD]; exact hb
  · rcases hD with hD | ⟨he, _⟩
    · exact hD.1
    · exfalso
      have hk : keeps c (s.agt a) = false := by
        cases hr : c.release <;> simp_all [keeps, Agent.live]
      have := reap_fold_ne (c := c) (a := a) c.tasks s ht (Or.inr ⟨h.1.1, h.1.2, hl, hk⟩)
      simp only [idleClaim, ownsClaimed, Bool.and_eq_true, beq_iff_eq] at h'
      rw [he] at h'
      exact this (by have h1 := h'.1.1; rw [tk_of_task (reapLocks_task _)] at h1; exact h1)
  · rcases hD with hD | ⟨_, _, hD, _⟩
    · exact hD.2.1
    · rw [hD]; exact hb
  · rcases hD with hD | ⟨_, _, _, hD⟩
    · exact hD.2.2
    · rw [hD]; exact hb

theorem forever (P : Nat → Prop) (m0 : Nat) (h0 : P m0) (hs : ∀ k, m0 ≤ k → P k → P (k + 1)) : ∀ k, m0 ≤ k → P k := by
  have : ∀ d, P (m0 + d) := fun d => by
    induction d with
    | zero => exact h0
    | succ d ih => exact hs _ (Nat.le_add_right ..) ih
  intro k hk
  have := this (k - m0); rwa [Nat.add_sub_cancel' hk] at this

theorem boot_works {c : Cfg} {s s' : State} {a : Nat} (hs : step c s (.boot a) = some s') (hi : (s.agt a).st = .idle) :
    (s'.agt a).st = .working := by
  have hl : a < s.ag.length := by
    refine Classical.byContradiction fun hl => ?_
    rw [agt_of_ge (Nat.le_of_not_lt hl)] at hi; exact absurd hi (by decide)
  simp only [step, boot, when, Option.ite_none_right_eq_some, Option.some.injEq] at hs
  obtain ⟨_, rfl⟩ := hs
  split
  · simp [agt_setAg, hl]
  · simp [agt_setAg, hl]

theorem expire_lapses {s s' : State} {t : Nat} {c : Cfg} (hs : step c s (.expire t) = some s') : (s'.tk t).lease = false := by
  simp only [step, expire, when, Option.ite_none_right_eq_some, Option.some.injEq] at hs
  obtain ⟨hc, rfl⟩ := hs
  have : (s.tk t).st ≠ .absent := by simp_all
  simp [tk_setTask_self this]

theorem Run.fair_ev {c : Cfg} {r : Run c} (hf : r.Fair) {f : Action} {N0 : Nat} (hm : ∀ k, N0 ≤ k → f ∈ fair c (r.st k))
    (hen : ∀ k, N0 ≤ k → (step c (r.st k) f).isSome) : ∃ k, N0 ≤ k ∧ r.act k = f :=
  hf f (fun N => ⟨max N N0, Nat.le_max_left .., hm _ (Nat.le_max_right ..), hen _ (Nat.le_max_right ..)⟩) N0

/-- L2. In a fair run of an instance with PR #110 or #111, a claim held by an idle agent doesn't stay so: its lease
lapses and the tick reopens the task, or the owner gets back to work. (A slot reused by a spawn is a new agent, who
boots at once.) -/
theorem idleClaim_leads_to {c : Cfg} (hr : c.racy = false) (hfix : c.release ≠ .ended) (hw : c.watchd = true) {a t : Nat}
    (ha : a ∈ c.agents) (ht : t ∈ c.tasks) (r : Run c) (hf : r.Fair) {n : Nat}
    (hq : ∀ k, n ≤ k → ∀ b, r.act k ≠ .bgStart b ∧ r.act k ≠ .die b)
    (hbg0 : ((r.st n).agt a).bg = false) (hdd0 : ((r.st n).agt a).dead = false)
    (h : idleClaim (r.st n) a t = true) : ∃ m, n ≤ m ∧ idleClaim (r.st m) a t = false := by
  refine Classical.byContradiction fun hne => ?_
  have hH : ∀ m, n ≤ m → idleClaim (r.st m) a t = true := fun m hm => by
    cases hx : idleClaim (r.st m) a t
    · exact absurd ⟨m, hm, hx⟩ hne
    · rfl
  have hidle : ∀ m, n ≤ m → ((r.st m).agt a).st = .idle := fun m hm => by
    have := hH m hm; simp [idleClaim] at this; exact this.2
  have hp : ∀ m, n ≤ m → ((r.st m).agt a).bg = false →
      (((r.st m).agt a).boot = true → ((r.st (m+1)).agt a).boot = true) ∧
      ((((r.st m).tk t).lease = false) → (((r.st (m+1)).tk t).lease = false ∨ ((r.st (m+1)).agt a).boot = true)) ∧
      (((r.st m).agt a).bg = false → ((r.st (m+1)).agt a).bg = false) ∧
      (((r.st m).agt a).dead = false → ((r.st (m+1)).agt a).dead = false) := by
    intro m hm hbg
    have hok := r.ok m
    by_cases hact : r.act m = .tick
    · rw [hact] at hok
      have := tick_persist hfix ht hbg (s := r.st m) (s' := r.st (m+1)) hok (hH m hm) (hH (m+1) (by omega))
      exact ⟨this.1, fun hl => Or.inr (this.2.1 hl), this.2.2.1, this.2.2.2⟩
    · have := persist hr hact (hq m hm) hok (hH m hm) (hH (m+1) (by omega))
      exact ⟨this.1, fun hl => Or.inl (this.2.1 hl), this.2.2.1, this.2.2.2⟩
  have hbgA : ∀ m, n ≤ m → ((r.st m).agt a).bg = false ∧ ((r.st m).agt a).dead = false := by
    refine forever (fun m => ((r.st m).agt a).bg = false ∧ ((r.st m).agt a).dead = false) n ⟨hbg0, hdd0⟩ ?_
    intro k hk ih
    have := hp k hk ih.1
    exact ⟨this.2.2.1 ih.1, this.2.2.2 ih.2⟩
  have hp' := fun m hm => hp m hm (hbgA m hm).1
  -- the agent isn't booting: a booting agent in an idle claim boots
  have hA : ∀ m, n ≤ m → ((r.st m).agt a).boot = false := by
    intro m0 hm0
    refine Classical.byContradiction fun hb => ?_
    have hb' : ((r.st m0).agt a).boot = true := by simpa using hb
    have hall := forever (fun k => ((r.st k).agt a).boot = true) m0 hb' (fun k hk ih => (hp' k (by omega)).1 ih)
    obtain ⟨k, hk, hact⟩ := Run.fair_ev hf (f := .boot a) (N0 := m0) (fun k hk => by simp [fair, ha, (hbgA k (by omega)).2]) (fun k hk => by
      have h1 := hall k hk
      have h2 := hidle k (by omega)
      simp [step, boot, when, h1, h2])
    have hok := r.ok k
    rw [hact] at hok
    have := boot_works hok (hidle k (by omega))
    have := hidle (k+1) (by omega)
    simp_all
  have hB : ∀ m, n ≤ m → ((r.st m).tk t).lease = false → ((r.st (m+1)).tk t).lease = false := by
    intro m hm hl
    rcases (hp' m hm).2.1 hl with e | e
    · exact e
    · have := hA (m+1) (by omega); simp_all
  by_cases hlapsed : ∃ m0, n ≤ m0 ∧ ((r.st m0).tk t).lease = false
  · obtain ⟨m0, hm0, hl0⟩ := hlapsed
    have hall := forever (fun k => ((r.st k).tk t).lease = false) m0 hl0 (fun k hk ih => hB k (by omega) ih)
    obtain ⟨k, hk, hact⟩ := Run.fair_ev hf (f := .tick) (N0 := m0) (fun k hk => by simp [fair]) (fun k hk => by
      have := tick_reopens (c := c) hfix hw ht (hH k (by omega)) (hall k hk) (hbgA k (by omega)).1
      simpa [step, tick, when, hw] using this)
    have hok := r.ok k
    rw [hact] at hok
    have := (tick_persist hfix ht (hbgA k (by omega)).1 (s := r.st k) (s' := r.st (k+1)) hok (hH k (by omega)) (hH (k+1) (by omega))).2.1 (hall k hk)
    have := hA (k+1) (by omega)
    simp_all
  · have hleased : ∀ k, n ≤ k → ((r.st k).tk t).lease = true := by
      intro k hk; cases hx : ((r.st k).tk t).lease
      · exact absurd ⟨k, hk, hx⟩ hlapsed
      · rfl
    obtain ⟨k, hk, hact⟩ := Run.fair_ev hf (f := .expire t) (N0 := n) (fun k hk => by simp [fair, ht]) (fun k hk => by
      have h1 := hleased k hk
      have h2 := hH k hk
      have h3 := hA k hk
      simp [step, expire, when, idleClaim, ownsClaimed] at h2 ⊢
      simp [h1, h2.1.1, bootingOwner, h2.1.2, h3])
    have hok := r.ok k
    rw [hact] at hok
    have := expire_lapses hok
    have := hleased (k+1) (by omega)
    simp_all

end Swarm

import SwarmModel.Fair

/-! L3, the reopened half, under `bootFirst` (a boot beats a lease): a spawned agent that holds the task reads its
answer at its first turn. Without `bootFirst` the lease lapses and a tick reaps the agent first (finding #17). -/

namespace Swarm
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.deprecated false

/-- what holds of a spawned agent `a` before its first turn, on the task it holds -/
def Booting (s : State) (a t : Nat) : Prop :=
  idleClaim s a t = true ∧ (s.agt a).boot = true ∧ (s.tk t).lease = true ∧ (s.tk t).answer = true ∧
    (s.agt a).waiter = false ∧ (s.agt a).dead = false

@[simp] theorem deliver_waiter (s : State) (a b : Nat) : ((deliver s a).agt b).waiter = (s.agt b).waiter := by
  obtain ⟨bl, e⟩ := deliver_agt s a b; rw [e]
@[simp] theorem takes_waiter (c : Cfg) (s : State) (a t b : Nat) : ((takes c s a t).agt b).waiter = (s.agt b).waiter := by
  obtain ⟨bl, e⟩ := takes_agt c s a t b; rw [e]

theorem leaveIf_keep {ok : Bool} {s s' : State} {a b t : Nat} (hs : leaveIf ok s b = some s') (hb : b ≠ a)
    (h : Booting s a t) : Booting s' a t := by
  simp only [leaveIf, when, Option.ite_none_right_eq_some, Option.some.injEq] at hs
  obtain ⟨hc, rfl⟩ := hs
  have hb' : ¬ a = b := fun e => hb e.symm
  obtain ⟨h, hb2, hl, hans, hw, hd⟩ := h
  simp only [idleClaim, ownsClaimed, Bool.and_eq_true, beq_iff_eq] at h
  simp [Booting, idleClaim, ownsClaimed, endAgent_agt, endAgent_tk, agt_setAg, setAg_tk, setAg_ag_length, held, hb, hb', h, hb2, hl, hans, hw, hd]

theorem holds_of {s : State} {a t : Nat} (hst : (s.tk t).st = .claimed) (ho : (s.tk t).owner = some a) : holds s a = true := by
  have h := tk_in_range (s := s) (t := t) (by rw [hst]; simp)
  simp only [holds, List.any_eq_true]
  refine ⟨s.task[t - 1], List.getElem_mem h.2, ?_⟩
  have e : s.tk t = s.task[t - 1] := by
    simp [State.tk, h.1, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h.2]
  rw [e] at hst ho
  simp [held, hst, ho]

/-- Any action but the tick, the boot, and the ones that end the agent's claim: a booting holder stays one. -/
theorem keep {c : Cfg} {s s' : State} {a t : Nat} {act : Action} (hr : c.racy = false) (hbf : c.bootFirst = true)
    (hn : act ≠ .tick ∧ act ≠ .boot a ∧ act ≠ .leave a ∧ act ≠ .reapGone a ∧ act ≠ .drop t ∧ act ≠ .releaseOther t ∧
      act ≠ .endOther a true)
    (hq : ∀ b, act ≠ .bgStart b ∧ act ≠ .die b)
    (hp : Pfx s) (hs : step c s act = some s') (h : Booting s a t) (hnd : (s'.tk t).st ≠ .done) : Booting s' a t := by
  have h0 := h
  obtain ⟨h, hb, hl, hans, hw, hd⟩ := h
  simp only [idleClaim, ownsClaimed, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hst, hown⟩, hidle⟩ := h
  obtain ⟨n1, n2, n3, n4, n5, n6, n7⟩ := hn
  cases act
  all_goals first | exact absurd rfl n1 | exact absurd rfl n2 | exact absurd rfl n3 | exact absurd rfl n4 | exact absurd rfl n5 | exact absurd rfl n6 | skip
  case bgStart => exact absurd rfl (hq _).1
  case die => exact absurd rfl (hq _).2
  case leave b =>
    simp only [step, leave] at hs
    exact leaveIf_keep hs (fun e => n3 (by rw [e])) h0
  case reapGone b =>
    simp only [step, reapGone] at hs
    exact leaveIf_keep hs (fun e => n4 (by rw [e])) h0
  case endOther b f =>
    simp only [step, endOther] at hs
    by_cases e : b = a
    · subst e
      cases f
      · simp [leaveIf, when, endable, holds_of hst hown] at hs
      · exact absurd rfl n7
    exact leaveIf_keep hs e h0
  case hcPrompt b =>
    simp only [step, hcPrompt, when, Option.ite_none_right_eq_some, Option.some.injEq] at hs
    obtain ⟨hc, rfl⟩ := hs
    have hne : b ≠ a := by rintro rfl; simp_all [busy]
    have hf : firstClaimed c s b ≠ t := by
      intro e
      by_cases h0 : firstClaimed c s b = 0
      · rw [e] at h0; subst h0; simp [State.tk] at hst
      · have := (fc_owns h0).2; rw [e, hown] at this; simp at this; exact hne this.symm
    have hf' : ¬ t = firstClaimed c s b := fun e => hf e.symm
    simp [Booting, idleClaim, ownsClaimed, setTask_agt, agt_setAg, setAg_tk, tk_setTask', hf', hst, hown, hidle, hb, hl, hans, hw, hd, hne]
  case hcClear b =>
    simp only [step, hcClear, when, Option.ite_none_right_eq_some, Option.some.injEq] at hs
    obtain ⟨hc, hs⟩ := hs
    have e1 : s'.tk t = s.tk t := by
      rw [← hs]; simp only [setAg_tk, deliver_tk]
      exact (tk_map (g := fun k => if (k.owner == some b && k.st == TSt.blocked && k.hcq) = true then
        { k with st := .claimed, lease := true, hcq := false } else k) (by simp) rfl t).trans (by simp [hst])
    have hne : a ≠ b := by rintro rfl; simp_all
    have e2 : ∃ bl, s'.agt a = { s.agt a with believes := bl } := by
      rw [← hs, agt_setAg, ite_eq_right_iff.2 (fun h => absurd h.1.symm hne)]; exact deliver_agt _ _ _
    obtain ⟨bl, e2⟩ := e2
    simp only [Booting, idleClaim, ownsClaimed, e1, e2]
    simp [hst, hown, hidle, hb, hl, hans, hw, hd]
  case unblock t₀ =>
    simp only [step, unblock] at hs
    split at hs
    · simp only [when, Option.ite_none_right_eq_some, Option.some.injEq] at hs
      obtain ⟨hc, hs⟩ := hs
      have hne : t ≠ t₀ := by rintro rfl; simp_all
      have e1 : s'.tk t = s.tk t := by rw [← hs]; simp only [tk_mk, tk_def]; exact tk_setTask_ne hne
      have e2 : s'.agt a = s.agt a := by rw [← hs]; simp only [agt_mk, agt_def, post_ag, setTask_ag]
      simp only [Booting, idleClaim, ownsClaimed, e1, e2]
      simp [hst, hown, hidle, hb, hl, hans, hw, hd]
    · simp at hs
  case add deps =>
    simp only [step, add, when, Option.ite_none_right_eq_some, Option.some.injEq] at hs
    obtain ⟨hc, rfl⟩ := hs
    obtain ⟨n, h2, h3⟩ := hp
    have habs : (s.tk (nextTask s)).st = .absent := by
      have := h3 (nextTask s)
      rw [nextTask_eq h2 h3] at this ⊢
      by_cases e : (s.tk (n + 1)).st = .absent
      · exact e
      · have := this.mp e; omega
    have hne : t ≠ nextTask s := by intro e; rw [e, habs] at hst; cases hst
    simpa [Booting, idleClaim, ownsClaimed, setTask_agt, tk_setTask_ne hne] using h0
  case expire t₀ =>
    simp only [step, expire, when, Option.ite_none_right_eq_some, Option.some.injEq] at hs
    obtain ⟨hc, rfl⟩ := hs
    have hne : t ≠ t₀ := by
      rintro rfl
      simp [hbf, bootingOwner, hown, hb] at hc
    simpa [Booting, idleClaim, ownsClaimed, setTask_agt, tk_setTask_ne hne] using h0
  case poll =>
    simp only [step, poll, when, Option.ite_none_right_eq_some, Option.some.injEq] at hs
    obtain ⟨_, rfl⟩ := hs
    rw [pollOf_tk] at hnd
    simp only [Booting, idleClaim, ownsClaimed, pollOf_agt, pollOf_tk]
    rcases prK_cases c s (s.tk t) with e | ⟨e1, e⟩ | ⟨_, _, e⟩ | ⟨_, _, e⟩ <;> rw [e] at hnd ⊢
    · simp [hst, hown, hidle, hb, hl, hans, hw, hd]
    · rw [hst] at e1; cases e1
    · exact absurd rfl hnd
    · simp [hst, hown, hidle, hb, hl, hans, hw, hd]
  all_goals (simp [step, claim, claimRead, claimWrite, renew, release, block, done, dropOwn, lock, unlock, postTo,
    readAll, stop, wake, wakeRead, wakeWrite, prompt, boot, waiterGone, age, cool, expire, expireLock,
    hcPrompt, hcClear, unblock, add, after, drop, releaseOther, endOther, awayOn, back, commsRead, when, hr, hbf, bgEnd, gitCmd, world, stale, nudge, hnudge, stay, endStay, stayCheck, stayHung,
    openPr, push, merge, finish, ciRun] at hs)
  all_goals (try obtain ⟨hc, rfl⟩ := hs)
  all_goals (try obtain ⟨hc, hs⟩ := hs)
  all_goals (try subst hs)
  all_goals (try simp_all [Booting, idleClaim, ownsClaimed, claimed, awake, unbelieve, tk_setTask', agt_setAg, setAg_ag_length, working, busy, held, claimable, startable])
  all_goals (try ((repeat' split at *) <;> simp_all))
  all_goals (try (simp_all [State.agt, State.tk]; done))
  all_goals (try (simp only [agt_setAg, deliver_ag_length, deliver_boot, deliver_st, deliver_bg, deliver_dead] at *; (repeat' split at *) <;> simp_all; done))
  all_goals (trace_state; done)

/-- the user's release of the task a booting agent holds leaves it owning no claimed `t` -/
theorem releaseOther_fc {c : Cfg} {s s' : State} {a t : Nat} (hs : step c s (.releaseOther t) = some s') (h : Booting s a t) :
    firstClaimed c s' a ≠ t := by
  simp only [step, releaseOther, when_eq_some] at hs
  obtain ⟨_, rfl⟩ := hs
  have hst : (s.tk t).st = .claimed := by simp [Booting, idleClaim, ownsClaimed] at h; exact h.1.1.1
  intro e
  have h0 : firstClaimed c (post (setTask s t (fun k => { k with st := .opn, owner := none, lease := false, hcq := false, stopTo := if c.stopFirst then k.owner else none, stopMsg := s.log.length + 1 }))
      ⟨none, (s.tk t).owner.getD 0, true, .released, t⟩) a ≠ 0 := by
    rw [e]; rintro rfl; simp [State.tk] at hst
  have := (fc_owns h0).1
  rw [e] at this
  simp only [State.tk, post_task] at this hst
  simp only [setTask] at this
  split at this
  · simp at hst; simp_all
  · rw [getD_modify] at this; split at this <;> simp_all

-- ---------- the tick ----------

theorem reapTask_keep {c : Cfg} {x : State} {t u : Nat} (h : (x.tk t).lease = true) : (reapTask c x u).tk t = x.tk t := by
  by_cases hu : t = u
  · subst hu
    unfold reapTask; simp only []
    split
    · simp [h]
    · rfl
  · exact reapTask_tk_ne hu

/-- what the tick leaves of a booting holder: the task, and the agent's turn state -/
def Q (a t : Nat) (z y : State) : Prop :=
  y.tk t = z.tk t ∧ (y.agt a).st = .idle ∧ (y.agt a).boot = true ∧ (y.agt a).waiter = false ∧ (y.agt a).dead = false

theorem Q_end {a t b : Nat} {z y : State} (ho : (z.tk t).owner = some a) (hb : b ≠ a) (h : Q a t z y) : Q a t z (endAgent y b) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hb' : ¬ a = b := fun e => hb e.symm
  simp only [Q, endAgent_tk, endAgent_agt, h1, held, ho, hb, hb', h2, h3, h4, h5]
  simp [hb, hb', h2, h3, h4, h5]

theorem Q_told {a t b : Nat} {z y : State} {m : Msg} {f : Agent → Agent}
    (hf : ∀ g, (f g).st = g.st ∧ (f g).boot = g.boot ∧ (f g).waiter = g.waiter ∧ (f g).dead = g.dead) (h : Q a t z y) :
    Q a t z (post (setAg y b f) m) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  simp only [Q, post_agt, post_tk, setAg_tk, agt_setAg, h1]
  by_cases hba : b = a ∧ a < y.ag.length
  · rw [if_pos hba]; simp [(hf _).1, (hf _).2.1, (hf _).2.2.1, (hf _).2.2.2, h2, h3, h4, h5]
  · rw [if_neg hba]; exact ⟨trivial, h2, h3, h4, h5⟩

theorem Q_spawn {c : Cfg} {a t t' : Nat} {pl : List Nat} {z y : State} (hpl : pl.contains t = false) (h : Q a t z y) :
    Q a t z (spawnFor c pl y t') := by
  by_cases e : t = t'
  · subst e; rw [spawnFor_not hpl]; exact h
  · obtain ⟨h1, h2, h3, h4, h5⟩ := h
    rcases spawnFor_agt c pl y t' a with ha | ⟨hn, _, _, _, _⟩
    · simp only [Q]; rw [ha, spawnFor_tk_ne e]; exact ⟨h1, h2, h3, h4, h5⟩
    · have := nextAgent_not_live hn
      simp [Agent.live, h2] at this

theorem lifecycle_Q {c : Cfg} {a t : Nat} {z : State} (hst : (z.tk t).st = .claimed) (ho : (z.tk t).owner = some a)
    (h0 : Q a t z z) : Q a t z (lifecycle c z) := by
  have hfin : finished c z a = false := by simp [finished, idleFree, holds_of hst ho]
  have hpl : (pool c z).contains t = false := by simp [pool, claimable, startable, hst]
  unfold lifecycle; simp only []
  have h2 := foldl_inv (fun y b => if finished c z b && !reusable c z b then endAgent y b else y) (Q a t z) c.agents z h0
    (fun y b hy => by
      split
      · rename_i hh
        refine Q_end ho (fun e => ?_) hy
        subst e; simp [hfin] at hh
      · exact hy)
  have h3 := foldl_inv (fun y b =>
    if reusable c z b && !(pool c z).all (y.agt b).told.contains then
      post (setAg y b fun g => { g with told := pool c z ++ g.told }) ⟨none, b, false, .digest, 0⟩
    else y) (Q a t z) c.agents _ h2 (fun y b hy => by split; exact Q_told (fun g => ⟨rfl, rfl, rfl, rfl⟩) hy; exact hy)
  split
  · exact h3
  · exact foldl_inv _ (Q a t z) _ _ h3 (fun y t' hy => Q_spawn hpl hy)

theorem tick_keep {c : Cfg} {s s' : State} {a t : Nat} (hs : tick c s = some s') (h : Booting s a t) : Booting s' a t := by
  have e : s' = tickOf c s := by simp [tick, when] at hs; exact hs.2.symm
  subst e
  obtain ⟨hi, hb, hl, hans, hw, hd⟩ := h
  simp only [idleClaim, ownsClaimed, Bool.and_eq_true, beq_iff_eq] at hi
  obtain ⟨⟨hst, hown⟩, hidle⟩ := hi
  have hz : (reapLocks (reapTasks c s)).tk t = s.tk t := by
    rw [tk_of_task (reapLocks_task _)]
    exact foldl_inv (reapTask c) (fun y : State => y.tk t = s.tk t) c.tasks s rfl
      (fun y u hy => by rw [reapTask_keep (by rw [hy]; exact hl), hy])
  have hza : (reapLocks (reapTasks c s)).agt a = s.agt a := by simp [State.agt]
  have hQ := lifecycle_Q (c := c) (a := a) (t := t) (z := reapLocks (reapTasks c s)) (by rw [hz]; exact hst) (by rw [hz]; exact hown)
    ⟨rfl, by rw [hza]; exact hidle, by rw [hza]; exact hb, by rw [hza]; exact hw, by rw [hza]; exact hd⟩
  obtain ⟨q1, q2, q3, q4, q5⟩ := hQ
  rw [hz] at q1
  obtain ⟨_, _, he⟩ := tickOf_ex c s; rw [he]
  show Booting (lifecycle c (reapLocks (reapTasks c s))) a t
  simp only [Booting, idleClaim, ownsClaimed, Bool.and_eq_true, beq_iff_eq, tickOf, q1]
  exact ⟨⟨⟨hst, hown⟩, q2⟩, q3, hl, hans, q4, q5⟩

-- ---------- the first turn ----------

/-- a booting holder's first turn reads the answer on the task it holds -/
theorem boot_reads {c : Cfg} {s s' : State} {a t : Nat} (hao : c.answerOnTask = true) (hfc : firstClaimed c s a = t)
    (hs : step c s (.boot a) = some s') (h : Booting s a t) : answered s' t = true := by
  obtain ⟨hi, hb, hl, hans, hw, hd⟩ := h
  simp only [idleClaim, ownsClaimed, Bool.and_eq_true, beq_iff_eq] at hi
  obtain ⟨⟨hst, hown⟩, hidle⟩ := hi
  have h0 : 0 < t := by
    rcases Nat.eq_zero_or_pos t with e | e
    · subst e; simp [State.tk] at hst
    · exact e
  simp only [step, boot, when, Option.ite_none_right_eq_some, Option.some.injEq] at hs
  obtain ⟨_, rfl⟩ := hs
  simp only [hfc, h0, if_true, takes, hao, answered]
  simp [hans]

/-- L3, the reopened half. With `bootFirst` (a boot beats a lease), a spawned agent that holds a task with an answer
on it reads the answer at its first turn, unless it leaves (or `swarm end --force` ends it), its terminal dies, or
the task is dropped: the tick can't
reap it first (finding #17), and it boots because `boot` is fair. `firstClaimed` is the task its first turn reads. -/
theorem booting_reads {c : Cfg} (hr : c.racy = false) (hbf : c.bootFirst = true) (hao : c.answerOnTask = true)
    {a t : Nat} (ha : a ∈ c.agents) (r : Run c) (hf : r.Fair) {n : Nat} (hR : Reachable c (r.st n))
    (hq : ∀ k, n ≤ k → (∀ b, r.act k ≠ .bgStart b ∧ r.act k ≠ .die b) ∧ r.act k ≠ .leave a ∧ r.act k ≠ .reapGone a ∧ r.act k ≠ .drop t
      ∧ r.act k ≠ .endOther a true)
    (hfc : ∀ k, n ≤ k → firstClaimed c (r.st k) a = t) (h : Booting (r.st n) a t) :
    ∃ m, answered (r.st m) t = true := by
  have hRk : ∀ k, n ≤ k → Reachable c (r.st k) := by
    intro k hk
    refine forever (fun k => Reachable c (r.st k)) n hR (fun k _ ih => ?_) k hk
    exact Reachable.step (r.act k) ih (r.ok k)
  by_cases hdn : ∃ k, n ≤ k ∧ ((r.st k).tk t).st = .done
  · obtain ⟨k, -, hk⟩ := hdn; exact ⟨k, by simp [answered, hk]⟩
  have hnd : ∀ k, n ≤ k → ((r.st k).tk t).st ≠ .done := fun k hk e => hdn ⟨k, hk, e⟩
  by_cases hex : ∃ k, n ≤ k ∧ r.act k = .boot a ∧ Booting (r.st k) a t
  · obtain ⟨k, hk, hact, hB⟩ := hex
    have := boot_reads hao (hfc k hk) (hact ▸ r.ok k) hB
    exact ⟨k + 1, this⟩
  · exfalso
    have hall : ∀ k, n ≤ k → Booting (r.st k) a t := by
      refine forever (fun k => Booting (r.st k) a t) n h (fun k hk ih => ?_)
      have hok := r.ok k
      by_cases ht : r.act k = .tick
      · rw [ht] at hok; exact tick_keep hok ih
      · have hb : r.act k ≠ .boot a := fun e => hex ⟨k, hk, e, ih⟩
        obtain ⟨q1, q2, q3, q4, q6⟩ := hq k hk
        have q5 : r.act k ≠ .releaseOther t := fun e => releaseOther_fc (e ▸ hok) ih (hfc (k + 1) (by omega))
        exact keep hr hbf ⟨ht, hb, q2, q3, q4, q5, q6⟩ q1 (pfx_of_reachable (hRk k hk)) hok ih (hnd (k + 1) (by omega))
    obtain ⟨k, hk, hact⟩ := Run.fair_ev hf (f := .boot a) (N0 := n) (fun k hk => by
        have := (hall k hk).2.2.2.2.2
        simp [fair, ha, this]) (fun k hk => by
        have h1 := hall k hk
        simp only [Booting, idleClaim, ownsClaimed, Bool.and_eq_true, beq_iff_eq] at h1
        simp [step, boot, when, h1.1.2, h1.2.1])
    exact hex ⟨k, hk, hact, hall k hk⟩

-- the hypothesis is met: after finding #17's prefix, the agent spawned into slot 0 for #1 is booting its claim
example : ((run { cfg17 with bootFirst := true } pre17).map fun s => idleClaim s 0 1 && (s.agt 0).boot && (s.tk 1).lease && (s.tk 1).answer && !(s.agt 0).waiter && !(s.agt 0).dead) = some true := by decide +kernel

end Swarm

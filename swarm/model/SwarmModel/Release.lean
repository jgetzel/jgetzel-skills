import SwarmModel.Answer

/-! H2 (board #40, #45): `swarm task release N` by the user or the communicator of a task another agent holds. In the
model the communicator's actions have no actor (as `unblock` and `drop`), so the user and the communicator are one
action, `releaseOther`, in `step`: S2-S5, N1, W1-W4 and L1-L4 are proved with it in. S1 is not: the user's release of a
working agent's task lets a peer claim it before the ex-owner reads the stop (`not_S1_humanRelease`), so S1 takes
`humanRelease` off (board task #53 is the fix). -/

namespace Swarm
set_option linter.unusedSimpArgs false

/-- the log only grows: every step appends to it -/
theorem step_log {c : Cfg} {s s' : State} {act : Action} (hs : step c s act = some s') : ∃ e, s'.log = s.log ++ e := by
  open_step hs
  case tick =>
    obtain ⟨_, rfl⟩ := hs
    exact tick_inv (fun x => ∃ e, x.log = s.log ++ e)
      (fun x t ⟨e, he⟩ => let ⟨e2, h2⟩ := reapTask_ext c x t; ⟨e ++ e2, by rw [h2, he]; simp⟩)
      (fun x h => by simpa using h) (fun x a h => by simpa using h)
      (fun x a pl ⟨e, he⟩ => ⟨e ++ [⟨none, a, false, .digest, 0⟩], by simp [post, he]⟩) (fun pl x t h _ => by simpa using h)
      ⟨[], by simp⟩
  case unblock t =>
    split at hs
    · rename_i o _
      rw [when_eq_some] at hs; obtain ⟨_, rfl⟩ := hs; exact ⟨[⟨none, o, false, .answer, t⟩], by simp [post]⟩
    · cases hs
  case postTo a b u => obtain ⟨_, rfl⟩ := hs; exact ⟨[⟨some a, b, u, .dm, 0⟩], by simp [post]⟩
  case nudge a => obtain ⟨_, rfl⟩ := hs; exact ⟨[⟨none, a, true, .nudge, 0⟩], by simp [post]⟩
  case releaseOther t => obtain ⟨_, rfl⟩ := hs; exact ⟨[⟨none, (s.tk t).owner.getD 0, true, .released, t⟩], by simp [post]⟩
  all_goals obtain ⟨_, rfl⟩ := hs
  all_goals ((repeat' split) <;> first
    | (refine ⟨[], ?_⟩; simp [unbelieve, awake]; done)
    | (refine ⟨[_], ?_⟩; simp [post, unbelieve, awake]; done))

/-- H2, the step: the user's release is enabled for any task an agent holds, claimed or blocked (by `task block` or an
hc prompt) -/
theorem releaseOther_enabled {c : Cfg} {s : State} {t o : Nat} (hh : c.humanRelease = true) (ho : held (s.tk t) o = true) :
    (step c s (.releaseOther t)).isSome := by
  simp only [held, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at ho
  simp [step, releaseOther, when, hh, ho.1, ho.2]

/-- H2, what it does: the task is open again, no owner, no hc prompt; its ex-owner `o` is sent an urgent stop (the last
message of the log, `.released` from the system or the communicator); nothing else on the board, no agent, no cursor
changes -/
theorem releaseOther_spec {c : Cfg} {s s' : State} {t : Nat} (hs : step c s (.releaseOther t) = some s') :
    ∃ o, held (s.tk t) o = true ∧ (s'.tk t).st = .opn ∧ (s'.tk t).owner = none ∧ (s'.tk t).hcq = false ∧
      s'.log = s.log ++ [⟨none, o, true, .released, t⟩] ∧ (∀ u, u ≠ t → s'.tk u = s.tk u) ∧ s'.ag = s.ag ∧
      s'.cursor = s.cursor := by
  simp only [step, releaseOther, when_eq_some, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hs
  obtain ⟨⟨⟨_, hsome⟩, hst⟩, rfl⟩ := hs
  obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp hsome
  have hna : (s.tk t).st ≠ .absent := by rcases hst with e | e <;> simp [e]
  refine ⟨o, by simp [held, ho, hst], ?_, ?_, ?_, by simp [post, ho], fun u hu => by rw [post_tk, tk_setTask_ne hu], by simp,
    by simp⟩ <;> simp [tk_setTask_self hna]

/-- H2, reading the stop: showing the ex-owner a `.released` message drops its belief that it holds the task, as for
reap's -/
theorem showMsg_released {s : State} {a i : Nat} (hk : (s.msg i).kind = .released) :
    (s.msg i).task ∉ ((showMsg s a i).agt a).believes := by
  have e1 : (Kind.released == Kind.answer) = false := rfl
  unfold showMsg
  simp only [hk, e1, beq_self_eq_true, Bool.false_and, Bool.false_eq_true, ite_false, ite_true]
  rw [agt_setAg]; split
  · simp
  · rename_i h
    have : ¬ a < s.ag.length := fun hl => h ⟨rfl, by simpa using hl⟩
    simp [State.agt, List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt this)]

/-- once shown, a belief never comes back by a message: showing more messages only drops beliefs -/
theorem showAll_believes_sub (a b u : Nat) : ∀ (ids : List Nat) (s : State), u ∈ ((showAll s a ids).agt b).believes →
    u ∈ (s.agt b).believes := by
  intro ids
  induction ids with
  | nil => intro s h; exact h
  | cons i is ih =>
    intro s h
    have h1 := ih _ h
    obtain ⟨bl, e⟩ := showMsg_agt s a i b
    unfold showMsg at h1 e
    simp only [] at h1 e
    split at h1
    · exact h1
    · split at h1
      · rw [agt_setAg] at h1; split at h1
        · rename_i hh; obtain ⟨rfl, _⟩ := hh; exact (List.mem_filter.mp h1).1
        · exact h1
      · exact h1

/-- H2, end to end: a delivery to the ex-owner that shows it the stop leaves it believing it holds the task no more -/
theorem deliver_released {s : State} {o i : Nat} (hi : i ∈ unread s o) (hk : (s.msg i).kind = .released) :
    (s.msg i).task ∉ ((deliver s o).agt o).believes := by
  unfold deliver
  obtain ⟨pre, post', hsplit⟩ := List.append_of_mem hi
  rw [hsplit, show showAll s o (pre ++ i :: post') = showAll (showMsg (showAll s o pre) o i) o post' by
    simp [showAll, List.foldl_append]]
  intro h
  have h2 := showAll_believes_sub o o _ post' _ h
  have hm : (showAll s o pre).msg i = s.msg i := msg_congr (showAll_log ..) i
  exact showMsg_released (s := showAll s o pre) (a := o) (i := i) (by rw [hm]; exact hk) (by rw [hm]; exact h2)

/-- H2, liveness. In a fair run, from a reachable state, an agent with an unread message (the user's stop) does not keep
at work unaware of it forever: at some later step it has read it (its cursor is past it), or it is not at work (idle,
ended, its slot another agent's), or its terminal is gone (which L4, `deadLive_leads_to`, then ends). Working, the
hook's `readAll` is fair; at an hc prompt, its answer (`hcClear`) is, and it delivers. -/
theorem stop_read {c : Cfg} (r : Run c) (hf : r.Fair) {n o i : Nat} (hR : Reachable c (r.st n))
    (hi : i ∈ unread (r.st n) o) :
    ∃ m, n ≤ m ∧ (active ((r.st m).agt o) = false ∨ ((r.st m).agt o).dead = true ∨ i ≤ (r.st m).cur o) := by
  refine Classical.byContradiction fun hne => ?_
  have hall : ∀ m, n ≤ m → active ((r.st m).agt o) = true ∧ ((r.st m).agt o).dead = false ∧ (r.st m).cur o < i :=
    fun m hm => by
      refine ⟨?_, ?_, ?_⟩
      · cases e : active ((r.st m).agt o); exact absurd ⟨m, hm, Or.inl e⟩ hne; rfl
      · cases e : ((r.st m).agt o).dead; rfl; exact absurd ⟨m, hm, Or.inr (Or.inl e)⟩ hne
      · exact Nat.lt_of_not_le fun e => hne ⟨m, hm, Or.inr (Or.inr e)⟩
  have hRk : ∀ k, n ≤ k → Reachable c (r.st k) :=
    forever _ n hR (fun k _ ih => Reachable.step (r.act k) ih (r.ok k))
  have hlog : ∀ k, n ≤ k → ∃ e, (r.st k).log = (r.st n).log ++ e :=
    forever _ n ⟨[], by simp⟩ (fun k _ ⟨e, he⟩ => by
      obtain ⟨e2, h2⟩ := step_log (r.ok k)
      exact ⟨e ++ e2, by rw [h2, he]; simp⟩)
  obtain ⟨_, hil, had⟩ := mem_unread.mp hi
  have hun : ∀ k, n ≤ k → i ∈ unread (r.st k) o := fun k hk => by
    obtain ⟨e, he⟩ := hlog k hk
    refine mem_unread.mpr ⟨(hall k hk).2.2, by rw [he]; simp; omega, ?_⟩
    simp only [addressed] at had ⊢; rw [msg_ext he hil]; exact had
  have hlive : ∀ k, n ≤ k → ((r.st k).agt o).live = true := fun k hk => by
    have := (hall k hk).1
    simp only [active, Bool.or_eq_true, beq_iff_eq] at this
    rcases this with e | e <;> simp [Agent.live, e]
  have hcl : ∀ k, n ≤ k → o < (r.st k).cursor.length := fun k hk => by
    rw [(i1_of_reachable (hRk k hk)).2.1, ← (i1_of_reachable (hRk k hk)).1]; exact lt_of_live (hlive k hk)
  have ha : o ∈ c.agents := mem_agents hR (hlive n (Nat.le_refl _))
  have hread : ∀ k, n ≤ k → ∀ x : State, (r.st (k + 1)) = x → unread x o ≠ [] := fun k hk x e => by
    rw [← e]; exact List.ne_nil_of_mem (hun (k + 1) (by omega))
  by_cases hwk : ∀ N, ∃ k ≥ N, ((r.st k).agt o).st = .working
  · obtain ⟨k, hk, hact⟩ := hf (.readAll o) (fun N => by
      obtain ⟨k, hk, hk2⟩ := hwk (max N n)
      refine ⟨k, by omega, by simp [fair, ha, (hall k (by omega)).2.1], ?_⟩
      have : unread (r.st k) o ≠ [] := List.ne_nil_of_mem (hun k (by omega))
      simp [step, readAll, when, busy, hk2, this]) n
    have hok := r.ok k; rw [hact] at hok
    simp only [step, readAll, when_eq_some] at hok
    exact hread k hk _ hok.2.symm (unread_deliver_self (hcl k hk))
  obtain ⟨N0, hN0⟩ : ∃ N0, ∀ k, N0 ≤ k → ((r.st k).agt o).st ≠ .working := by
    refine Classical.byContradiction fun hh => hwk fun N => ?_
    exact Classical.byContradiction fun h2 => hh ⟨N, fun k hk hk2 => h2 ⟨k, hk, hk2⟩⟩
  have hbk : ∀ k, max n N0 ≤ k → ((r.st k).agt o).st = .blocked := fun k hk => by
    have h1 := (hall k (by omega)).1; have h2 := hN0 k (by omega)
    simp only [active, Bool.or_eq_true, beq_iff_eq] at h1
    rcases h1 with e | e
    · exact absurd e h2
    · exact e
  obtain ⟨k, hk, hact⟩ := Run.fair_ev hf (f := .hcClear o) (N0 := max n N0)
    (fun k hk => by simp [fair, ha, (hall k (by omega)).2.1]) (fun k hk => by simp [step, hcClear, when, hbk k hk])
  have hok := r.ok k; rw [hact] at hok
  simp only [step, hcClear, when_eq_some] at hok
  obtain ⟨_, hok⟩ := hok
  apply hread k (by omega) _ hok.symm
  rw [show ∀ (x : State) (f : Agent → Agent), unread (setAg x o f) o = unread x o from fun _ _ => rfl]
  exact unread_deliver_self (by simpa using hcl k (by omega))

/-- H2's stop is such a message: right after the user's release its ex-owner has it unread -/
theorem releaseOther_unread {c : Cfg} {s s' : State} {t : Nat} (hR : Reachable c s) (hs : step c s (.releaseOther t) = some s') :
    ∃ o, held (s.tk t) o = true ∧ s'.log.length ∈ unread s' o ∧ (s'.msg s'.log.length).kind = .released ∧
      (s'.msg s'.log.length).task = t ∧ (s'.msg s'.log.length).urgent = true := by
  obtain ⟨o, ho, _, _, _, hlog, _, _, hcur⟩ := releaseOther_spec hs
  have hc : s.cur o ≤ s.log.length := (inbInv_of_reachable hR).2.2 o |>.1
  have hm : s'.msg s'.log.length = ⟨none, o, true, .released, t⟩ := by
    simp [State.msg, hlog, List.getD_eq_getElem?_getD]
  refine ⟨o, ho, mem_unread.mpr ⟨?_, Nat.le_refl _, ?_⟩, by rw [hm], by rw [hm], by rw [hm]⟩
  · have : s'.cur o = s.cur o := by simp [State.cur, hcur]
    rw [this, hlog]; simp; omega
  · simp [addressed, hm]

/-- H2 and liveness together: after the user's release, its ex-owner reads the stop, or is not at work, or its terminal
is gone, at some step of any fair run -/
theorem released_reads {c : Cfg} (r : Run c) (hf : r.Fair) {n t : Nat} (hR : Reachable c (r.st n))
    (hact : r.act n = .releaseOther t) :
    ∃ o i, held ((r.st n).tk t) o = true ∧ ((r.st (n + 1)).msg i).kind = .released ∧ ((r.st (n + 1)).msg i).task = t ∧
      ∃ m, n + 1 ≤ m ∧ (active ((r.st m).agt o) = false ∨ ((r.st m).agt o).dead = true ∨ i ≤ (r.st m).cur o) := by
  have hok := r.ok n; rw [hact] at hok
  obtain ⟨o, ho, hu, hk, ht, _⟩ := releaseOther_unread hR hok
  exact ⟨o, _, ho, hk, ht, stop_read r hf (Reachable.step _ hR hok) hu⟩

-- ---------- the finding: H2 breaks S1 ----------

/-- two agents at work, one task -/
def cfgH2 : Cfg := { nagents := 2, roster := 2, ntasks := 1 }

/-- Agent 0 claims #1 and works on it; the user releases #1 (agent 0 is sent the stop, unread: its next tool's hook would
show it); agent 1 claims #1. Both are at work, both believe they hold #1. -/
theorem not_S1_humanRelease : (run cfgH2 [.add [], .claim 0 1, .releaseOther 1, .claim 1 1]).map oneWorker = some false := by
  decide

/-- with H2 off the release isn't there, and S1 holds (`oneWorker_of_reachable`) -/
example : run { cfgH2 with humanRelease := false } [.add [], .claim 0 1, .releaseOther 1] = none := by decide

/-- H2 is enabled for a task blocked by an hc prompt too, and the answered prompt doesn't take it back: the task stays
open, and the ex-owner reads the stop as the prompt clears -/
example : ((run cfgH2 [.add [], .claim 0 1, .hcPrompt 0, .releaseOther 1, .hcClear 0]).map fun s =>
    ((s.tk 1).st, (s.tk 1).owner, (s.agt 0).believes, unread s 0)) = some (.opn, none, [], []) := by decide

end Swarm

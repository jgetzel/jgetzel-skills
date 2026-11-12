import SwarmModel.Away

/-! Stays (board #79). `swarm stay "<what>"` and `swarm stay --end` (the agent's own, `stay a on`), `swarm stay --end A`
(the user or the communicator, `endStay a`) and watchd's liveness check of an idle stayer (`stayCheck`, then `stayHung`
when it is not answered) are actions of `step`, so S1-S5, N1, W1-W4, L1-L4, H1, H2 and A1-A4 are proved with them in.
Lifecycle keeps a stayer (`stayer_kept`, `tick_keeps_stayer`: fate's `stay`), and `swarm end` without `--force` refuses
one (`endOther_stay`). The check goes to the stayer once per idle stretch; unanswered, the stayer's `stay-hung` is
logged and the communicator told, urgent, once (`stayCheck_spec`, `stayHung_spec`). `--back`'s digest lists the agents
hung since away and not ended since (`digest_hung`). -/

namespace Swarm

/-- a stayer is not finished: lifecycle neither ends nor reuses it -/
theorem stayer_kept {c : Cfg} {s : State} {a : Nat} (h : (s.agt a).stay = true) :
    finished c s a = false ∧ ends c s a = false ∧ reusable c s a = false := by
  have hf : finished c s a = false := by simp [finished, idleFree, h]
  exact ⟨hf, by simp [ends, hf], by simp [reusable, hf]⟩

/-- the tick keeps a live stayer: its row as it was but for the pool ids a digest told it of (not ended, its slot no
spawn's) -/
theorem tick_keeps_stayer {c : Cfg} {s : State} {a : Nat} (hs : (s.agt a).stay = true) (hl : (s.agt a).live = true) :
    { (tickOf c s).agt a with told := [] } = { s.agt a with told := [] } := by
  have hz : (reapLocks (reapTasks c s)).agt a = s.agt a := agt_of_ag (by simp) a
  have := lifecycle_keeps (c := c) (stayer_kept (c := c) (by rw [hz]; exact hs)).1 (by rw [hz]; exact hl)
  obtain ⟨_, _, he⟩ := tickOf_ex c s; rw [he]
  show { (lifecycle c (reapLocks (reapTasks c s))).agt a with told := [] } = _
  rw [this, hz]

/-- `swarm end A` without `--force` refuses a stayer (watchd.end_why's "stays for") -/
theorem endOther_stay {c : Cfg} {s : State} {a : Nat} (h : (s.agt a).stay = true) : step c s (.endOther a false) = none := by
  simp [step, endOther, leaveIf, when, endable, h]

/-- `swarm stay` and `stay --end`: the agent's own, at work, its stay flag alone -/
theorem stay_spec {c : Cfg} {s s' : State} {a : Nat} {on : Bool} (h : step c s (.stay a on) = some s') :
    working s a = true ∧ s' = setAg s a ({ · with stay := on }) := by
  simp only [step, stay, when_eq_some] at h; exact ⟨h.1, h.2.symm⟩

/-- `swarm stay --end A` is enabled exactly for a live stayer, and clears its stay alone -/
theorem endStay_spec {c : Cfg} {s s' : State} {a : Nat} (h : step c s (.endStay a) = some s') :
    (s.agt a).live = true ∧ (s.agt a).stay = true ∧ s' = setAg s a ({ · with stay := false }) := by
  simp only [step, endStay, when_eq_some, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2.symm⟩
theorem endStay_enabled (c : Cfg) (s : State) (a : Nat) :
    (step c s (.endStay a)).isSome = ((s.agt a).live && (s.agt a).stay) := by
  simp only [step, endStay, when]; split <;> simp_all

/-- the liveness check: to an idle stayer with a live waiter, not cold, not yet checked in this idle stretch; one message
to it, not urgent, and it is checked -/
theorem stayCheck_spec {c : Cfg} {s s' : State} {a : Nat} (h : step c s (.stayCheck a) = some s') :
    (s.agt a).stay = true ∧ (s.agt a).st = .idle ∧ (s.agt a).waiter = true ∧ (s.agt a).cold = false ∧
    (s.agt a).checked = false ∧ s'.log = s.log ++ [⟨none, a, false, .check, 0⟩] ∧ (s'.agt a).checked = true := by
  simp only [step, stayCheck, when_eq_some, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨_, h1⟩, h2⟩, _⟩, h4⟩, h5⟩, h6⟩, rfl⟩ := h
  refine ⟨h1, h2, h5, h4, h6, by simp [post], ?_⟩
  simp [post, lt_of_idle h2]

/-- unanswered, the stayer is hung: `stay-hung` logged and the communicator told, urgent; then not again in this idle
stretch -/
theorem stayHung_spec {c : Cfg} {s s' : State} {a : Nat} (h : step c s (.stayHung a) = some s') :
    (s.agt a).stay = true ∧ (s.agt a).st = .idle ∧ (s.agt a).checked = true ∧ s'.evs = s.evs ++ [.hung a] ∧
    s'.cbox = s.cbox ++ [⟨.hung, a, true, []⟩] ∧ step c s' (.stayHung a) = none := by
  simp only [step, stayHung, when_eq_some, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨_, h1⟩, h2⟩, _⟩, h4⟩, _⟩, rfl⟩ := h
  refine ⟨h1, h2, h4, rfl, rfl, ?_⟩
  simp [step, stayHung, when, agt_setAg, lt_of_idle h2]

/-- the last of a's hung and ended events is a hung: a hung with no end of a after it -/
theorem lastHung_iff (a : Nat) (L : List Ev) :
    (match (L.filter fun e => e == .hung a || e == .ended a).getLast? with | some (.hung _) => true | _ => false) = true ↔
      ∃ l1 l2, L = l1 ++ .hung a :: l2 ∧ Ev.ended a ∉ l2 := by
  -- a decomposition of L ++ [e] whose hung is not e: one of L, e after it
  have split_last : ∀ (L : List Ev) (e : Ev), e ≠ .hung a → ∀ l1 l2, L ++ [e] = l1 ++ .hung a :: l2 →
      ∃ l2', l2 = l2' ++ [e] ∧ L = l1 ++ .hung a :: l2' := by
    intro L e he l1 l2 h
    rcases List.eq_nil_or_concat l2 with rfl | ⟨l2', x, rfl⟩
    · have := (List.append_inj' h rfl).2; simp at this; exact absurd this he
    · have h' : L ++ [e] = (l1 ++ .hung a :: l2') ++ [x] := by simpa using h
      obtain ⟨h1, h2⟩ := List.append_inj' h' rfl
      simp at h2; subst h2; exact ⟨l2', by simp, h1⟩
  obtain ⟨R, rfl⟩ : ∃ R, L = R.reverse := ⟨L.reverse, by simp⟩
  induction R with
  | nil => simp
  | cons e R ih =>
    generalize hL : R.reverse = L at ih
    rw [List.reverse_cons, hL, List.filter_append]
    by_cases he1 : e = .hung a
    · subst he1
      simp only [List.filter_cons, List.filter_nil, beq_self_eq_true, Bool.true_or, ite_true, List.getLast?_append,
        List.getLast?_singleton, Option.some_or]
      exact ⟨fun _ => ⟨L, [], rfl, by simp⟩, fun _ => trivial⟩
    by_cases he2 : e = .ended a
    · subst he2
      simp only [List.filter_cons, List.filter_nil, beq_self_eq_true, Bool.or_true, ite_true, List.getLast?_append,
        List.getLast?_singleton, Option.some_or, Bool.false_eq_true, false_iff, not_exists, not_and]
      intro l1 l2 h hn
      obtain ⟨l2', rfl, _⟩ := split_last L _ (by simp) l1 l2 h
      exact hn (by simp)
    · have hp : (e == .hung a || e == .ended a) = false := by simp [he1, he2]
      simp only [List.filter_cons, List.filter_nil, hp, Bool.false_eq_true, ite_false, List.append_nil]
      refine ih.trans ⟨?_, ?_⟩
      · rintro ⟨l1, l2, rfl, hn⟩; exact ⟨l1, l2 ++ [e], by simp, by simp [hn, Ne.symm he2]⟩
      · rintro ⟨l1, l2, h, hn⟩
        obtain ⟨l2', rfl, h'⟩ := split_last L e he1 l1 l2 h
        exact ⟨l1, l2', h', fun hm => hn (by simp [hm])⟩

/-- `--back`'s hung (agents.digest's: a `stay-hung` event after the away event's, its agent not ended): a slot is listed
exactly when its agent hung since `since` and no end of that slot came after (a slot's next agent is another row) -/
theorem digest_hung (c : Cfg) (s : State) (since a : Nat) :
    a ∈ (digestOf c s since).hung ↔
      a < c.nagents ∧ ∃ l1 l2, s.evs.drop since = l1 ++ .hung a :: l2 ∧ Ev.ended a ∉ l2 := by
  simp only [digestOf, List.mem_filter, Cfg.agents, List.mem_range, hungSince]
  exact and_congr_right fun _ => lastHung_iff a _

end Swarm

import SwarmModel.Inbox
import SwarmModel.NoWorkLost
import SwarmModel.Findings
import SwarmModel.Restart
import SwarmModel.Cut

/-! What each Bool checker of the model checks, with its definition unfolded into ∀, ∃, ∧, ∨ (board #86, STYLE.md).
`Contract.lean` names these right-hand sides (`OneWorkerPerTask`, `HoldsWork`, …) and cites the lemma here as the
named Prop's iff; a named Prop that drifts from what is proved here stops unifying and breaks the build. The replay
and the counterexamples keep running the checkers. -/

namespace Swarm

theorem oneWorker_spec (s : State) : oneWorker s = true ↔
    ∀ a b t, (((s.agt a).st = .working ∨ (s.agt a).st = .blocked) ∧ t ∈ (s.agt a).believes) →
      (((s.agt b).st = .working ∨ (s.agt b).st = .blocked) ∧ t ∈ (s.agt b).believes) → a = b := by
  have act : ∀ a, active (s.agt a) = true ↔ ((s.agt a).st = .working ∨ (s.agt a).st = .blocked) := fun a => by
    simp [active]
  have lt : ∀ a, active (s.agt a) = true → a < s.ag.length := fun a h =>
    Classical.byContradiction fun hl => by rw [agt_of_ge (Nat.le_of_not_lt hl)] at h; exact absurd h (by decide)
  simp only [oneWorker, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true',
    Bool.and_eq_false_iff, List.any_eq_false, List.contains_iff_mem, ← act]
  constructor
  · intro h a b t ⟨ha, hta⟩ ⟨hb, htb⟩
    rcases h a (lt a ha) b (lt b hb) with e | (e | e) | e
    · exact e
    · rw [ha] at e; cases e
    · rw [hb] at e; cases e
    · exact absurd htb (e t hta)
  · intro h a _ b _
    refine Classical.byContradiction fun hn => ?_
    simp only [not_or, Bool.not_eq_false, Classical.not_forall, Classical.not_not] at hn
    obtain ⟨hab, ⟨ha, hb⟩, t, hta, htb⟩ := hn
    exact hab (h a b t ⟨ha, hta⟩ ⟨hb, htb⟩)

theorem holdsWork_spec (c : Cfg) (s : State) (a : Nat) : holdsWork c s a = true ↔
    (s.agt a).live = true ∧
      ((s.agt a).bg = true
        ∨ (∃ w, wtmap c s a = some w ∧ s.git.landedIn (abases c s a) w = false)
        ∨ ∃ w gen, (w, gen) ∈ (s.agt a).own ∧ owns s a w = true ∧ s.git.landedIn (abases c s a) w = false) := by
  simp [holdsWork, or_assoc, Option.any_eq_true]

theorem keptBy_spec (s s' : State) (a : Nat) :
    keptBy s s' a = true ↔ { s'.agt a with told := [] } = { s.agt a with told := [] } := by
  simp [keptBy]

theorem deadLive_spec (s : State) (a : Nat) :
    deadLive s a = true ↔ (s.agt a).live = true ∧ (s.agt a).dead = true := by
  simp [deadLive]

theorem midTick_spec (w : World) (i p : Nat) : midTick w i p = true ↔ w.tkOf i = some p ∧ w.alive p = true := by
  simp [midTick]

theorem held_spec (k : Task) (a : Nat) : held k a = true ↔ k.owner = some a ∧ (k.st = .claimed ∨ k.st = .blocked) := by
  simp [held]

theorem stopped_spec (s : State) (t : Nat) : stopped s t = true ↔
    ∃ o, (s.tk t).stopTo = some o ∧ ((s.agt o).st = .working ∨ (s.agt o).st = .blocked) ∧ s.cur o < (s.tk t).stopMsg := by
  unfold stopped
  cases h : (s.tk t).stopTo <;> simp [active, h]

theorem noEarlyStart_spec (s : State) : noEarlyStart s = true ↔ s.early = false := by
  simp [noEarlyStart]

theorem inboxExact_spec (s : State) : inboxExact s = true ↔ ∀ a, a < s.ag.length →
    (s.seen.getD a []).Pairwise (· < ·) ∧
      ∀ i, s.start.getD a 0 < i → i ≤ s.cur a → (s.msg i).to = a → (s.msg i).frm ≠ some a → i ∈ s.seen.getD a [] := by
  simp only [inboxExact, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true,
    Bool.not_eq_true', List.mem_range'_1, List.contains_iff_mem, addressed, Bool.and_eq_false_iff, bne_eq_false_iff_eq,
    beq_eq_false_iff_ne, ne_eq]
  refine forall_congr' fun a => forall_congr' fun _ => and_congr Iff.rfl ?_
  constructor
  · intro h i h1 h2 h3 h4
    rcases h i ⟨by omega, by omega⟩ with (e | e) | e
    · exact absurd h3 e
    · exact absurd e h4
    · exact e
  · intro h i hi
    by_cases h3 : (s.msg i).to = a
    · by_cases h4 : (s.msg i).frm = some a
      · exact Or.inl (Or.inr h4)
      · exact Or.inr (h i (by omega) (by omega) h3 h4)
    · exact Or.inl (Or.inl h3)

theorem doneHasEvidence_spec (s : State) : doneHasEvidence s = true ↔ ∀ k ∈ s.task, k.st = .done → k.ev = true := by
  simp [doneHasEvidence, List.all_eq_true, Bool.or_eq_true]
  exact forall_congr' fun k => forall_congr' fun _ => by cases k.ev <;> simp [or_comm]

theorem used_spec (c : Cfg) (s : State) (w : Nat) : used c s w = true ↔
    ∃ b ∈ c.agents, (s.agt b).live = true ∧ ((s.agt b).wt = some w ∨ wtmap c s b = some w) := by
  simp [used, List.any_eq_true]

theorem gcOk_spec (c : Cfg) (s : State) (g' : Git) : gcOk c s g' = true ↔
    (∀ w ∈ c.wtIds, (s.git.wt w).on = true → (g'.wt w).on = false →
      (s.git.wt w).dirty = false ∧ (¬ ∃ b ∈ c.agents, (s.agt b).live = true ∧ ((s.agt b).wt = some w ∨ wtmap c s b = some w)) ∧
        (s.git.wt w).proc = false ∧ s.git.safe c (s.git.wt w).head = true) ∧
    ∀ b < s.git.brs.length, (∃ k, s.git.tip b = some k) → g'.tip b = none →
      c.nbases ≤ b ∧ s.git.safe c (s.git.tipOf b) = true := by
  have hu := used_spec c s
  unfold gcOk
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    Bool.and_eq_false_iff, decide_eq_true_eq]
  refine and_congr (forall_congr' fun w => forall_congr' fun _ => ?_) (forall_congr' fun b => forall_congr' fun _ => ?_)
  · have hn : used c s w = false ↔ ¬ ∃ b ∈ c.agents, (s.agt b).live = true ∧ ((s.agt b).wt = some w ∨ wtmap c s b = some w) := by
      rw [Bool.eq_false_iff, ne_eq, hu w]
    rw [← hn]
    cases h1 : (s.git.wt w).on <;> cases h2 : (g'.wt w).on <;> cases h3 : (s.git.wt w).dirty <;>
      cases h4 : (s.git.wt w).proc <;> cases h5 : used c s w <;> cases h6 : Git.safe c s.git (s.git.wt w).head <;> simp
  · cases h1 : s.git.tip b <;> cases h2 : g'.tip b <;> simp

theorem unlanded_spec (c : Cfg) (s : State) (a : Nat) : unlanded c s a = true ↔
    (∃ w, wtmap c s a = some w ∧ landedC c s.git (abases c s a) w = false) ∨
    (c.allWts = true ∧ ((s.agt a).recorded = false ∨ c.ownAdded = true) ∧
      ∃ p ∈ (s.agt a).own, owns s a p.1 = true ∧ landedC c s.git (abases c s a) p.1 = false) ∨
    ∃ k, (s.agt a).rhead = some k ∧ landedK c s.git ((s.agt a).rbase :: abases c s a) k = false := by
  simp [unlanded, Option.any_eq_true, List.any_eq_true, or_assoc, and_assoc]

theorem endable_spec (c : Cfg) (s : State) (a : Nat) : endable c s a = true ↔
    (s.agt a).st = .idle ∧ (s.agt a).stay = false ∧
      (¬ ∃ k ∈ s.task, k.owner = some a ∧ (k.st = .claimed ∨ k.st = .blocked)) ∧
      (¬ ∃ l ∈ s.lock, l.holder = some a) ∧ (s.agt a).bg = false ∧
      ¬ ((∃ w, wtmap c s a = some w ∧ landedC c s.git (abases c s a) w = false) ∨
        (c.allWts = true ∧ ((s.agt a).recorded = false ∨ c.ownAdded = true) ∧
          ∃ p ∈ (s.agt a).own, owns s a p.1 = true ∧ landedC c s.git (abases c s a) p.1 = false) ∨
        ∃ k, (s.agt a).rhead = some k ∧ landedK c s.git ((s.agt a).rbase :: abases c s a) k = false) := by
  rw [← unlanded_spec]
  simp [endable, holds, lockHeld, held, List.any_eq_true, and_assoc]

theorem idleClaim_spec (s : State) (a t : Nat) : idleClaim s a t = true ↔
    ((s.tk t).st = .claimed ∧ (s.tk t).owner = some a) ∧ (s.agt a).st = .idle := by
  simp [idleClaim, ownsClaimed]

theorem last_filter {α : Type} (p : α → Bool) (l : List α) (x : α) (h : (l.filter p).getLast? = some x) :
    ∃ l1 l2, l = l1 ++ x :: l2 ∧ p x = true ∧ ∀ e ∈ l2, p e = false := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    by_cases hf : l.filter p = []
    · have hall : ∀ e ∈ l, p e = false := fun e he => by simpa using List.filter_eq_nil_iff.mp hf e he
      by_cases ha : p a = true
      · simp [List.filter_cons, ha, hf] at h
        subst h
        exact ⟨[], l, rfl, ha, hall⟩
      · simp [List.filter_cons, ha, hf] at h
    · have h' : (l.filter p).getLast? = some x := by
        cases hl : l.filter p with
        | nil => exact absurd hl hf
        | cons y ys =>
          by_cases ha : p a = true
          · simpa [List.filter_cons, ha, hl, List.getLast?_cons_cons] using h
          · simpa [List.filter_cons, ha, hl] using h
      obtain ⟨l1, l2, e, hx, hl⟩ := ih h'
      exact ⟨a :: l1, l2, by simp [e], hx, hl⟩

theorem toldAfter_spec (evs : List Ev) (t : Nat) : toldAfter evs t = true ↔
    ∃ l1 l2 b, evs = l1 ++ Ev.tblocked t b :: l2 ∧ ∀ e ∈ l2, e ≠ .block t ∧ ∀ b', e ≠ .tblocked t b' := by
  have hq : ∀ e, isQ t e = false ↔ e ≠ .block t ∧ ∀ b', e ≠ .tblocked t b' := fun e => by
    simp only [isQ, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, fun b => by cases b <;> assumption⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, h2 true⟩, h2 false⟩
  constructor
  · intro h
    unfold toldAfter at h
    cases hl : (evs.filter (isQ t)).getLast? with
    | none => simp [hl] at h
    | some x =>
      obtain ⟨l1, l2, e, hx, hl2⟩ := last_filter _ _ _ hl
      simp only [hl] at h
      cases x with
      | tblocked u b =>
        simp only [isQ, Bool.or_eq_true, beq_iff_eq] at hx
        have : u = t := by rcases hx with (h | h) | h <;> cases h <;> rfl
        subst this
        exact ⟨l1, l2, b, e, fun z hz => (hq z).mp (hl2 z hz)⟩
      | _ => simp at h
  · rintro ⟨l1, l2, b, e, hl⟩
    have : (evs.filter (isQ t)).getLast? = some (Ev.tblocked t b) := by
      subst e
      have h2 : l2.filter (isQ t) = [] := List.filter_eq_nil_iff.mpr fun z hz => by simpa using (hq z).mpr (hl z hz)
      cases b <;> simp [List.filter_append, h2, isQ]
    simp [toldAfter, this]

theorem active_spec (g : Agent) : active g = true ↔ (g.st = .working ∨ g.st = .blocked) := by
  simp [active]

/-! The older forms of the two S1 statements about `believes`, which `Contract.lean` restates and proves from. -/

theorem believes_held_of {c : Cfg} (hfix : c.release = .idle) (hhr : c.humanRelease = false) {s : State}
    (h : Reachable c s) {a t : Nat} (ha : active (s.agt a) = true) (ht : t ∈ (s.agt a).believes) :
    held (s.tk t) a = true ∨ (s.tk t).st = .dropped ∨ ((s.tk t).st = .done ∧ (s.tk t).merged = true) := by
  rcases (J_of_reachable hfix (Or.inl hhr) h).1 a t ht with hi | hd | hs
  · exact absurd hi.1 (by simp [ha])
  · exact hd
  · have := hs.1.1; rw [stopTo_none hhr h] at this; cases this

theorem believes_held_stop_of {c : Cfg} (hfix : c.release = .idle) (hsf : c.stopFirst = true) {s : State}
    (h : Reachable c s) {a t : Nat} (ha : active (s.agt a) = true) (ht : t ∈ (s.agt a).believes) :
    held (s.tk t) a = true ∨ (s.tk t).st = .dropped ∨ ((s.tk t).st = .done ∧ (s.tk t).merged = true) ∨
      ((s.tk t).st = .opn ∧ stopped s t = true) := by
  rcases (J_of_reachable hfix (Or.inr hsf) h).1 a t ht with hi | hd | hs
  · exact absurd hi.1 (by simp [ha])
  · rcases hd with e | e | e
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr (Or.inl e))
  · refine Or.inr (Or.inr (Or.inr ⟨hs.2, ?_⟩))
    unfold stopped; rw [hs.1.1]; simp [ha, hs.1.2.1]

end Swarm

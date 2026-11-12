import SwarmModel.Inbox
import SwarmModel.NoWorkLost
import SwarmModel.Findings
import SwarmModel.Restart

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

end Swarm

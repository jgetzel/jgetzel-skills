import SwarmModel.Workers
import SwarmModel.Findings

/-! L2, as far as it is proved: with either fix of finding #1, a claim whose owner is idle is never stuck. Its
lease can still lapse, or watchd's next tick reopens it and tells the owner. -/

namespace Swarm
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem reapTask_log_le (c : Cfg) (x : State) (t : Nat) : x.log.length ≤ (reapTask c x t).log.length := by
  unfold reapTask; simp only []; split
  · split
    · simp
    · exact Nat.le_refl _
  · exact Nat.le_refl _
theorem reapTask_tk_ne {c : Cfg} {x : State} {t u : Nat} (h : u ≠ t) : (reapTask c x t).tk u = x.tk u := by
  unfold reapTask; simp only []; split
  · split
    · show (setTask x t _).tk u = x.tk u
      exact tk_setTask_ne h
    · rfl
  · rfl
theorem reapTask_fires {c : Cfg} {x : State} {t a : Nat} (hst : (x.tk t).st = .claimed) (ho : (x.tk t).owner = some a)
    (hl : (x.tk t).lease = false) (hk : keeps c (x.agt a) = false) : (reapTask c x t).log.length = x.log.length + 1 := by
  unfold reapTask; simp [ho, hst, hl, hk]

theorem reap_fold_le (c : Cfg) : ∀ (l : List Nat) (x : State), x.log.length ≤ (l.foldl (reapTask c) x).log.length
  | [], _ => Nat.le_refl _
  | t :: ts, x => Nat.le_trans (reapTask_log_le c x t) (reap_fold_le c ts _)
theorem reap_fold_lt {c : Cfg} {t a : Nat} : ∀ (l : List Nat) (x : State), t ∈ l → (x.tk t).st = .claimed →
    (x.tk t).owner = some a → (x.tk t).lease = false → keeps c (x.agt a) = false →
    x.log.length < (l.foldl (reapTask c) x).log.length
  | [], _, hm, _, _, _, _ => by cases hm
  | u :: us, x, hm, hst, ho, hl, hk => by
    simp only [List.foldl_cons]
    by_cases hu : t = u
    · subst hu
      have := reapTask_fires hst ho hl hk
      have := reap_fold_le c us (reapTask c x t)
      omega
    · have hm' : t ∈ us := by
        rcases List.mem_cons.mp hm with e | e
        · exact absurd e hu
        · exact e
      have e := reapTask_tk_ne (c := c) (x := x) (t := u) (u := t) hu
      have := reap_fold_lt us (reapTask c x u) hm' (by rw [e]; exact hst) (by rw [e]; exact ho) (by rw [e]; exact hl)
        (by rw [State.agt, reapTask_ag]; exact hk)
      have := reapTask_log_le c x u
      omega

theorem lifecycle_log_le (c : Cfg) (x : State) : x.log.length ≤ (lifecycle c x).log.length := by
  unfold lifecycle; simp only []
  have h2 := foldl_inv (fun y a => if finished c x a && !reusable c x a then endAgent y a else y)
    (fun y : State => x.log.length ≤ y.log.length) c.agents x (Nat.le_refl _) (fun b a hb => by
      split
      · simpa using hb
      · exact hb)
  have h3 := foldl_inv (fun y a =>
    if reusable c x a && !(pool c x).all (y.agt a).told.contains then
      post (setAg y a fun g => { g with told := pool c x ++ g.told }) ⟨none, a, false, .digest, 0⟩
    else y) (fun y : State => x.log.length ≤ y.log.length) c.agents _ h2 (fun b a hb => by
      split
      · simp; omega
      · exact hb)
  split
  · exact h3
  · exact foldl_inv _ (fun y : State => x.log.length ≤ y.log.length) _ _ h3 (fun b t hb => by simpa using hb)

/-- With PR #110 or #111: once the lease of a claim whose owner is idle has lapsed, watchd's tick does something
(reap reopens the task and posts `released` to the owner). -/
theorem tick_reopens {c : Cfg} {s : State} {a t : Nat} (hfix : c.release ≠ .ended) (ht : t ∈ c.tasks)
    (hic : idleClaim s a t = true) (hl : (s.tk t).lease = false) (hbg : (s.agt a).bg = false) : tickOf c s ≠ s := by
  simp [idleClaim, ownsClaimed] at hic
  have hk : keeps c (s.agt a) = false := by
    cases hr : c.release <;> simp_all [keeps, Agent.live]
  have h1 : s.log.length < (reapTasks c s).log.length := reap_fold_lt c.tasks s ht hic.1.1 hic.1.2 hl hk
  have h2 := lifecycle_log_le c (reapLocks (reapTasks c s))
  rw [reapLocks_log] at h2
  intro e
  have h3 : (lifecycle c (reapLocks (reapTasks c s))).log.length = s.log.length := congrArg (·.log.length) e
  omega

/-- L2, the part that is proved. With PR #110 or #111, a state where an idle agent holds a claim is not stuck: the
lease can lapse, or the tick is enabled. (That every fair run then reaches "done or open again" is not proved.) -/
theorem idleClaim_not_stuck {c : Cfg} {s : State} {a t : Nat} (hfix : c.release ≠ .ended) (ht : t ∈ c.tasks)
    (ha : a ∈ c.agents) (hic : idleClaim s a t = true) : stuck c s = false := by
  cases hs : stuck c s
  · rfl
  · exfalso
    simp only [stuck, List.all_eq_true] at hs
    have h1 := hs .tick (by simp [fair])
    have h2 := hs (.expire t) (by simp [fair, ht])
    simp [step, tick, when] at h1
    simp [step, expire, when] at h2
    have hic' := hic
    simp [idleClaim, ownsClaimed] at hic'
    have h3 := hs (.bgEnd a) (by simp [fair, ha])
    have hbg : (s.agt a).bg = false := by
      cases hb : (s.agt a).bg
      · rfl
      · exfalso; simp [step, bgEnd, when, Agent.live, hb] at h3
        simp [idleClaim, ownsClaimed] at hic; simp [hic.2] at h3
    exact tick_reopens hfix ht hic (by simpa [hic'.1.1] using h2) hbg h1

end Swarm

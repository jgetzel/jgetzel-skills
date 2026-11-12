import SwarmModel.Answer

/-! PRs in the main model (board #80): P1 and P2 of `Model.lean`'s `step`, where a task's PR, main's CI and watchd's poll
(`poll`, ci.pr_watch and ci.pr_ci) are part of the state and the run, beside leases, reaping, spawns and the rest.
`PrWatch.lean` states them of a layer of its own and refutes them with each fix off; here they are proved of the model
the other properties are proved of, over its fair runs (`Run.Fair`, the poll in `fair`).

Both have one shape (`poll_ends`): while a condition holds the poll is enabled, and the poll ends it, so on a fair run
it does not hold forever. P2: a task claimed with its PR merged is marked done. P1: in a pr-gated repo the owner of a
claimed task whose PR's checks finished is told, by an urgent message (its waiter wakes it on that: `wakes`, and `wake`
is fair); the stayer's wait is #79's. Both need the owner live, which `HeldLive` (L3I) gives a reachable state. -/

namespace Swarm

/-- the fair poll fires while `C` holds, and its step ends `C`: `C` does not hold from some point on forever -/
theorem poll_ends {c : Cfg} (hw : c.watchd = true) (r : Run c) (hf : r.Fair) {C : State → Prop}
    (hC : ∀ s, C s → pollOf c s ≠ s ∧ ¬ C (pollOf c s)) (n : Nat) (h : ∀ m, n ≤ m → C (r.st m)) : False := by
  obtain ⟨k, hk, ha⟩ := hf .poll (fun N => ⟨max N n, Nat.le_max_left .., by simp [fair], by
    have := (hC _ (h (max N n) (Nat.le_max_right ..))).1
    simp [step, poll, when, hw, this]⟩) n
  have hok := r.ok k
  rw [ha] at hok
  simp only [step, poll, when, Option.ite_none_right_eq_some, Option.some.injEq] at hok
  exact (hC _ (h k hk)).2 (hok.2 ▸ h (k + 1) (by omega))

theorem reach_run {c : Cfg} (r : Run c) {n : Nat} (hR : Reachable c (r.st n)) : ∀ m, n ≤ m → Reachable c (r.st m) :=
  forever (fun k => Reachable c (r.st k)) n hR (fun k _ ih => Reachable.step (r.act k) ih (r.ok k))

/-- o holds t claimed, and t's PR (opened) is merged -/
def mergedClaimed (s : State) (o t : Nat) : Prop := ownsClaimed s o t = true ∧ (s.tk t).pr.opened = true ∧ (s.tk t).pr.merged = true
/-- P2 (every flow): on a fair run from a reachable state, a task claimed with its PR merged does not stay so -/
def P2 (c : Cfg) : Prop := ∀ r : Run c, r.Fair → Reachable c (r.st 0) →
  ∀ n o t, mergedClaimed (r.st n) o t → ∃ m ≥ n, ¬ mergedClaimed (r.st m) o t

/-- o holds t claimed, its PR open with a verdict on its head (green or red), and watchd hasn't told o of it -/
def untold (s : State) (o t : Nat) : Prop :=
  ownsClaimed s o t = true ∧ (s.tk t).pr.opened = true ∧ (s.tk t).pr.checks ≠ .pending ∧ (s.tk t).pr.merged = false ∧
    (s.tk t).pr.told = false
/-- P1 (pr-gated): on a fair run from a reachable state, the owner of a claimed task whose PR's checks finished is told:
the poll sends it one urgent message (`.checks`) and marks the head told -/
def P1 (c : Cfg) : Prop := ∀ r : Run c, r.Fair → Reachable c (r.st 0) →
  ∀ n o t, untold (r.st n) o t → ∃ m ≥ n, ¬ untold (r.st m) o t

theorem owner_live {c : Cfg} (hr : c.racy = false) (hbf : c.bootFirst = true) (hao : c.answerOnTask = true) {s : State}
    (hR : Reachable c s) {o t : Nat} (h : ownsClaimed s o t = true) : (s.agt o).live = true := by
  simp only [ownsClaimed, Bool.and_eq_true, beq_iff_eq] at h
  exact (l3_of_reachable hr hbf hao hR).2.1 t o (by simp [held, h.1, h.2])

theorem pollOf_ne {c : Cfg} {s : State} {t : Nat} (h : prK c s (s.tk t) ≠ s.tk t) : pollOf c s ≠ s := by
  intro e; apply h; rw [← pollOf_tk, e]

/-- P2 with main's fixes (racy off, PR #110's answer on the task, a boot beats a lease) and watchd running -/
theorem P2_of {c : Cfg} (hr : c.racy = false) (hbf : c.bootFirst = true) (hao : c.answerOnTask = true)
    (hw : c.watchd = true) : P2 c := by
  intro r hf h0 n o t hm
  apply Classical.byContradiction; intro hno
  have hall : ∀ m, n ≤ m → Reachable c (r.st m) ∧ mergedClaimed (r.st m) o t := fun m hm' =>
    ⟨reach_run r h0 m (Nat.zero_le _), Classical.byContradiction fun e => hno ⟨m, hm', e⟩⟩
  refine poll_ends hw r hf (C := fun s => Reachable c s ∧ mergedClaimed s o t) (fun s ⟨hR, hc⟩ => ?_) n hall
  have hl := owner_live hr hbf hao hR hc.1
  obtain ⟨h1, h2, h3⟩ := hc
  simp only [ownsClaimed, Bool.and_eq_true, beq_iff_eq] at h1
  have hd : (prK c s (s.tk t)).st = .done := by simp [prK, prAct, h1.1, h1.2, hl, h2, h3]
  refine ⟨pollOf_ne (fun e => by rw [e, h1.1] at hd; cases hd), fun ⟨_, h1', _⟩ => ?_⟩
  simp only [ownsClaimed, Bool.and_eq_true, beq_iff_eq, pollOf_tk] at h1'
  rw [hd] at h1'; cases h1'.1

/-- P1 in a pr-gated repo, with main's fixes and watchd running -/
theorem P1_of {c : Cfg} (hr : c.racy = false) (hbf : c.bootFirst = true) (hao : c.answerOnTask = true)
    (hw : c.watchd = true) (hg : c.gated = true) : P1 c := by
  intro r hf h0 n o t hu
  apply Classical.byContradiction; intro hno
  have hall : ∀ m, n ≤ m → Reachable c (r.st m) ∧ untold (r.st m) o t := fun m hm' =>
    ⟨reach_run r h0 m (Nat.zero_le _), Classical.byContradiction fun e => hno ⟨m, hm', e⟩⟩
  refine poll_ends hw r hf (C := fun s => Reachable c s ∧ untold s o t) (fun s ⟨hR, hc⟩ => ?_) n hall
  have hl := owner_live hr hbf hao hR hc.1
  obtain ⟨h1, h2, h3, h4, h5⟩ := hc
  simp only [ownsClaimed, Bool.and_eq_true, beq_iff_eq] at h1
  have hd : (prK c s (s.tk t)).pr.told = true := by simp [prK, prAct, h1.1, h1.2, hl, h2, bne_iff_ne, h3, h4, h5, hg]
  refine ⟨pollOf_ne (fun e => by rw [e, h5] at hd; cases hd), fun ⟨_, _, _, _, _, h5'⟩ => ?_⟩
  rw [pollOf_tk, hd] at h5'; cases h5'

/-- P1 and P2 of the main model as main runs it (`Cfg`'s defaults), P1 in a pr-gated repo -/
theorem main_P2 : P2 ({} : Cfg) := P2_of rfl rfl rfl rfl
theorem main_P1 : P1 ({ gated := true } : Cfg) := P1_of rfl rfl rfl rfl rfl

end Swarm

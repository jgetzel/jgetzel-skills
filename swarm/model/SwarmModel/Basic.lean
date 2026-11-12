import SwarmModel.Frame

/-! S2 and S5, for every reachable state of every instance with the fix on. -/

namespace Swarm

theorem when_eq_some {b : Bool} {x s' : State} : when b x = some s' ↔ b = true ∧ x = s' := by
  unfold when; split <;> simp_all

/-- turn `step c s act = some s'` into the action's guard and `s' = ..`, one goal per action -/
macro "open_step" h:ident : tactic => `(tactic|
  (cases ‹Action› <;>
   simp only [step, bgStart, bgEnd, claim, claimRead, claimWrite, renew, release, block, done, dropOwn, lock, unlock, postTo, readAll,
     stop, wake, wakeRead, wakeWrite, prompt, boot, waiterGone, age, cool, expire, expireLock, leave, leaveIf, hcPrompt,
     hcClear, die, reapGone, gitCmd, world, stale, nudge, hnudge, add, after, unblock, drop, releaseOther, endOther, awayOn, back, commsRead, tick, when_eq_some] at $h:ident))

/-- An invariant of reachable states: true at the start, kept by every step. -/
theorem reachable_induct {c : Cfg} {P : State → Prop} (h0 : P (init c))
    (hstep : ∀ s s' act, Reachable c s → P s → step c s act = some s' → P s') {s : State} (h : Reachable c s) : P s := by
  induction h with
  | init => exact h0
  | step act hr hs ih => exact hstep _ _ act hr ih hs

/-- S2. With PR #112 (claim's write rechecks the dependencies), no task starts before the tasks it is after are done. -/
theorem noEarlyStart_of_reachable {c : Cfg} (hfix : c.claimChecksDeps = true) {s : State} (h : Reachable c s) :
    noEarlyStart s = true := by
  suffices s.early = false by simp [noEarlyStart, this]
  refine reachable_induct (P := fun s => s.early = false) rfl ?_ h
  intro s s' act _ hs hstep
  open_step hstep
  case unblock t => split at hstep <;> simp_all [when_eq_some] <;> (obtain ⟨_, rfl⟩ := hstep; simp [hs])
  all_goals (obtain ⟨hg, rfl⟩ := hstep; (try split) <;> simp_all)

-- ---------- S5 ----------
def EvL (l : List Task) : Prop := ∀ k ∈ l, k.st = .done → k.ev = true
/-- a change of one task that keeps "done has evidence" -/
def EvKeeps (f : Task → Task) : Prop := ∀ k, (k.st = .done → k.ev = true) → (f k).st = .done → (f k).ev = true

theorem evL_modify {l : List Task} {f : Task → Task} (i : Nat) (h : EvL l) (hf : EvKeeps f) : EvL (l.modify i f) := by
  intro k hk
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hk
  rw [List.getElem?_modify] at hj
  split at hj
  · cases hl : l[j]? with
    | none => simp [hl] at hj
    | some k0 => simp [hl] at hj; subst hj; exact hf k0 (h k0 (List.mem_of_getElem? hl))
  · simp at hj; exact h k (List.mem_of_getElem? hj)
theorem evL_map {l : List Task} {f : Task → Task} (h : EvL l) (hf : EvKeeps f) : EvL (l.map f) := by
  intro k hk
  obtain ⟨k0, hk0, rfl⟩ := List.mem_map.mp hk
  exact hf k0 (h k0 hk0)
theorem evL_setTask {s : State} {f : Task → Task} (t : Nat) (h : EvL s.task) (hf : EvKeeps f) : EvL (setTask s t f).task := by
  unfold setTask; split
  · exact h
  · exact evL_modify _ h hf
theorem evL_releaseAll {s : State} (a : Nat) (h : EvL s.task) : EvL (releaseAll s a).task :=
  evL_map h (by intro k hk; dsimp only; split <;> simp_all)
theorem evL_reapTask {c : Cfg} {s : State} (t : Nat) (h : EvL s.task) : EvL (reapTask c s t).task := by
  unfold reapTask; simp only []; split
  · split
    · simp only [post_task]; exact evL_setTask _ h (by intro k hk; simp)
    · exact h
  · exact h
theorem evL_endAgent {s : State} (a : Nat) (h : EvL s.task) : EvL (endAgent s a).task := by
  simp only [endAgent]; exact evL_releaseAll _ (by simpa using h)
theorem evL_tickOf {c : Cfg} {s : State} (h : EvL s.task) : EvL (tickOf c s).task := by
  have hend : ∀ x a, EvL x.task → EvL (endAgent x a).task := fun x a hx => evL_endAgent a hx
  have hspawn : ∀ pl x t, EvL x.task → EvL (spawnFor c pl x t).task := fun pl x t hx => by
    unfold spawnFor; split
    · split
      · exact evL_setTask _ (by simpa using hx) (by intro k hk; simp)
      · exact hx
    · exact hx
  have h1 : EvL (reapLocks (reapTasks c s)).task := by
    simp only [reapLocks_task]; exact foldl_inv _ (fun x : State => EvL x.task) _ _ h (fun b t hb => evL_reapTask t hb)
  rw [tickOf_task]; unfold tickS lifecycle
  generalize reapLocks (reapTasks c s) = s1 at h1 ⊢
  have h2 := foldl_inv (fun x a => if finished c s1 a && !reusable c s1 a then endAgent x a else x)
    (fun x : State => EvL x.task) c.agents s1 h1 (fun b a hb => by split; exact hend _ _ hb; exact hb)
  have h3 := foldl_inv (fun x a =>
    if reusable c s1 a && !(pool c s1).all (x.agt a).told.contains then
      post (setAg x a fun g => { g with told := pool c s1 ++ g.told }) ⟨none, a, false, .digest, 0⟩
    else x) (fun x : State => EvL x.task) c.agents _ h2 (fun b a hb => by split <;> simpa using hb)
  simp only []
  split
  · exact h3
  · exact foldl_inv _ (fun x : State => EvL x.task) _ _ h3 (fun b t hb => hspawn _ _ _ hb)

/-- S5. With PR #113 (task done refuses empty evidence), every done task has evidence. -/
theorem doneHasEvidence_of_reachable {c : Cfg} (hfix : c.evidenceRequired = true) {s : State} (h : Reachable c s) :
    doneHasEvidence s = true := by
  suffices EvL s.task by
    simp only [doneHasEvidence, List.all_eq_true]
    intro k hk
    by_cases hd : k.st = .done <;> simp [hd, this k hk]
  refine reachable_induct (P := fun s => EvL s.task) ?_ ?_ h
  · intro k hk; rw [List.eq_of_mem_replicate hk]; intro hd; cases hd
  intro s s' act _ hs hstep
  open_step hstep
  case unblock t =>
    split at hstep
    · rw [when_eq_some] at hstep; obtain ⟨_, rfl⟩ := hstep; simp; exact evL_setTask _ hs (by intro k hk; simp)
    · cases hstep
  case tick => obtain ⟨_, rfl⟩ := hstep; exact evL_tickOf hs
  case leave a => obtain ⟨_, rfl⟩ := hstep; exact evL_endAgent _ (by simpa using hs)
  case reapGone a => obtain ⟨_, rfl⟩ := hstep; exact evL_endAgent _ (by simpa using hs)
  case endOther a f => obtain ⟨_, rfl⟩ := hstep; exact evL_endAgent _ (by simpa using hs)
  case hcClear a => obtain ⟨_, rfl⟩ := hstep; simp; exact evL_map hs (by intro k hk; dsimp only; split <;> simp_all)
  case done a t ev => obtain ⟨hg, rfl⟩ := hstep; simp; exact evL_setTask _ hs (by intro k hk; simp_all)
  all_goals
    obtain ⟨hg, rfl⟩ := hstep
    (try split) <;> first
      | (simpa using hs)
      | (simp; exact evL_setTask _ hs (by intro k hk; simp_all))
      | (simp [claimed]; exact evL_setTask _ hs (by intro k hk; simp_all))
      | exact evL_setTask _ (by simpa using hs) (by intro k hk; simp_all)

end Swarm

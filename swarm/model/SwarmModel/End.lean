import SwarmModel.NoWorkLost

/-! H1 (board #40, #46): `swarm end A` by the user or the communicator (watchd.cmd_end) is the action `endOther` of `step`,
so S1-S5, N1, W1-W4 and L1-L4 are proved with it in. Without `--force` it makes lifecycle's checks but the 2 min idle,
whoever runs it (`endable`, `finished_eq`; the Lua's check lifted: `Decide.endWhy_lifted`), so it ends no agent that holds
work (`N1end_of`), and it changes nothing but that agent's row (`endOther_spec`). `--force` is `leave`
(`endOther_force`): it ends an agent mid-job (finding #33, `not_N1end_force`). Neither touches git (`endOther_git`). -/

namespace Swarm

/-- `swarm end A --force` is `leave` of A: the checks skipped, A's row ended, its claims and locks released -/
theorem endOther_force (c : Cfg) (s : State) (a : Nat) : step c s (.endOther a true) = step c s (.leave a) := rfl

/-- lifecycle's `finished` (with `bgLives`) is `swarm end`'s check and the 2 min idle, between the model's ghost reads -/
theorem finished_eq {c : Cfg} (hb : c.bgLives = true) (s : State) (a : Nat) :
    finished c s a = (endable c s a && (s.agt a).aged && (s.agt a).reading == 0 && (s.agt a).snap.isEmpty) := by
  simp only [finished, idleFree, endable, hb, Bool.true_and]
  cases ((s.agt a).st == .idle) <;> cases (s.agt a).aged <;> cases (s.agt a).stay <;> cases holds s a <;> cases lockHeld s a <;>
    cases ((s.agt a).reading == 0) <;> cases (s.agt a).snap.isEmpty <;> cases unlanded c s a <;> cases (s.agt a).bg <;> rfl

/-- H1: `swarm end A` without --force is enabled exactly when its check passes (between the model's ghost reads) -/
theorem endOther_enabled {c : Cfg} {s : State} {a : Nat} :
    (step c s (.endOther a false)).isSome = (endable c s a && (s.agt a).reading == 0 && (s.agt a).snap.isEmpty) := by
  have hl : endable c s a = true → (s.agt a).live = true := fun h => by
    simp only [endable, Bool.and_eq_true, beq_iff_eq] at h; simp [Agent.live, h.1.1.1.1.1]
  simp only [step, endOther, leaveIf, when, Bool.false_or]
  by_cases he : endable c s a = true
  · simp only [he, hl he, Bool.true_and]; split <;> simp_all
  · simp [he]

/-- releasing what an agent holds nothing of changes nothing -/
theorem releaseAll_free {s : State} {a : Nat} (hh : holds s a = false) (hl : lockHeld s a = false) : releaseAll s a = s := by
  simp only [holds, List.any_eq_false] at hh
  simp only [lockHeld, List.any_eq_false] at hl
  have ht : s.task.map (fun k => if held k a then { k with st := .opn, owner := none, lease := false, hcq := false } else k)
      = s.task := by
    conv => rhs; rw [← List.map_id s.task]
    exact List.map_congr_left fun k hk => by simp [hh k hk]
  have hk : s.lock.map (fun l => if l.holder == some a then (⟨none, false⟩ : Lock) else l) = s.lock := by
    conv => rhs; rw [← List.map_id s.lock]
    exact List.map_congr_left fun l hl' => by simp at hl; simp [hl l hl']
  simp only [releaseAll, ht, hk]

/-- H1: `swarm end A` without --force ends A only when its check passes, and changes nothing but A's row: no task, lock,
message, cursor or git ref; A ended, every other agent as it was -/
theorem endOther_spec {c : Cfg} {s s' : State} {a : Nat} (h : step c s (.endOther a false) = some s') :
    endable c s a = true ∧ s'.task = s.task ∧ s'.lock = s.lock ∧ s'.log = s.log ∧ s'.cursor = s.cursor ∧ s'.git = s.git ∧
      (a < s.ag.length → (s'.agt a).st = .ended) ∧ ∀ b, b ≠ a → s'.agt b = s.agt b := by
  simp only [step, endOther, leaveIf, when_eq_some, Bool.false_or, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨he, _⟩, _⟩, _⟩, rfl⟩ := h
  have he' := he
  simp only [endable, Bool.and_eq_true, Bool.not_eq_true'] at he'
  obtain ⟨⟨⟨⟨_, hh⟩, hl⟩, _⟩, _⟩ := he'
  have hz := releaseAll_free (s := setAg (logEv (setAg s a fun g => { g with waiter := false }) (.ended a)) a
    fun g => { g with st := .ended, boot := false, believes := [] }) (a := a)
    (by simpa [holds] using hh) (by simpa [lockHeld] using hl)
  refine ⟨he, ?_, ?_, ?_, ?_, ?_, fun ha => ?_, fun b hb => ?_⟩
  all_goals simp only [endAgent, hz, setAg_task, setAg_lock, setAg_log, setAg_cursor, setAg_git, logEv_task, logEv_lock,
    logEv_log, logEv_cursor, logEv_git]
  · rw [agt_setAg]; simp [ha]
  · rw [agt_setAg, logEv_agt, agt_setAg]; simp [Ne.symm hb]

/-- `swarm end`, forced or not, removes no worktree and deletes no branch: what it leaves in a worktree only workspace GC
may remove, and W1 says GC removes nothing unlanded -/
theorem endOther_git {c : Cfg} {s s' : State} {a : Nat} {f : Bool} (h : step c s (.endOther a f) = some s') : s'.git = s.git := by
  simp only [step, endOther, leaveIf, when_eq_some] at h
  obtain ⟨_, rfl⟩ := h
  simp

/-- N1 of `swarm end` (board #46): `swarm end A` by the user or the communicator never ends an agent that holds work (a
background job running, or work off its tasks' bases in a worktree it works in or owns) -/
def N1end (c : Cfg) (force : Bool) : Prop :=
  ∀ s s' a, Reachable c s → step c s (.endOther a force) = some s' → holdsWork c s a = false

/-- N1end without --force, on the landed checks of main (PR #123's `allWts`, board #15's `ownAdded`, per-task bases):
`swarm end`'s check is lifecycle's, so what lifecycle keeps (`finished_of_holds`) it refuses -/
theorem N1end_of {c : Cfg} (haw : c.allWts = true) (hoa : c.ownAdded = true) (hp : c.perTaskBase = true) : N1end c false := by
  intro s s' a _ h
  have he := (endOther_spec h).1
  have e : ∀ refs w, landedC c s.git refs w = s.git.landedIn refs w := fun _ _ => by simp [landedC, hp]
  cases hw : holdsWork c s a
  · rfl
  exfalso
  simp only [holdsWork, Bool.and_eq_true, Bool.or_eq_true] at hw
  simp only [endable, Bool.and_eq_true, Bool.not_eq_true'] at he
  obtain ⟨⟨⟨⟨_, _⟩, _⟩, hbg⟩, hu⟩ := he
  obtain ⟨_, (hb | hw') | ho⟩ := hw
  · rw [hb] at hbg; cases hbg
  · have : unlanded c s a = true := by simp only [unlanded, e, hw', Bool.true_or]
    rw [this] at hu; cases hu
  · have : unlanded c s a = true := by simp only [unlanded, e, ho, haw, hoa, Bool.or_true, Bool.and_true, Bool.true_or]
    rw [this] at hu; cases hu

/-- where the run ends, agent a holds work and `swarm end a` (forced or not) is enabled -/
def endBreaks (c : Cfg) (acts : List Action) (a : Nat) (force : Bool) : Bool :=
  (run c acts).any fun s => holdsWork c s a && (step c s (.endOther a force)).isSome

theorem not_N1end {c : Cfg} {acts : List Action} {a : Nat} {f : Bool} (h : endBreaks c acts a f = true) : ¬ N1end c f := by
  intro hN
  unfold endBreaks at h
  cases e : run c acts with
  | none => simp [e] at h
  | some s =>
    simp only [e, Option.any_some, Bool.and_eq_true] at h
    obtain ⟨hw, hs⟩ := h
    obtain ⟨s', hs'⟩ := Option.isSome_iff_exists.mp hs
    rw [hN s s' a (reachable_of_run e) hs'] at hw; cases hw

/-- #33: agent 0 starts a long job (a build, a CI wait); the user runs `swarm end m-1 --force`: the row is ended mid-job,
and end_agent's cgroup.kill kills the job. The user's explicit choice to lose work -/
def pre33 : List Action := [.bgStart 0]
theorem not_N1end_force : ¬ N1end {} true := not_N1end (by decide : endBreaks {} pre33 0 true = true)
/-- #33 too: agent 0 holds an uncommitted file in its worktree and stops; `--force` ends it, the file stays (`endOther_git`) -/
def pre33w : List Action := [.git 0 (.add 0), .git 0 (.edit 0), .stop 0 false]
theorem not_N1end_force_wt : ¬ N1end { nwts := 1, perTaskBase := true, ownAdded := true } true :=
  not_N1end (by decide : endBreaks { nwts := 1, perTaskBase := true, ownAdded := true } pre33w 0 true = true)
-- without --force `swarm end` refuses both ("has a background job running", "has work not on its base")
example : endBreaks {} pre33 0 false = false := by decide
example : endBreaks { nwts := 1, perTaskBase := true, ownAdded := true } pre33w 0 false = false := by decide

/-- board #63 (#46's replay): agent 1 lands a commit on `formal`; agent 0 is spawned for task 1, on `formal`, and the user
releases it. Agent 0's recorded worktree is at formal's tip, not on main, the base it falls back to; since board #78 it is
checked against its workspace's base too (`rbase`), so `swarm end` ends it, as it does one spawned for a task on main -/
def cfg63 : Cfg := { nwts := 1, nbases := 2, perTaskBase := true, recordedWorkspaces := true, taskBase := [0, 1] }
def pre63 : List Action := [.git 1 (.add 0), .git 1 (.edit 0), .git 1 (.commit 0), .git 1 (.land 0 1),
  .stop 0 false, .age 0, .tick, .add [], .tick, .releaseOther 1]
example : (run cfg63 pre63).any (fun s => (step cfg63 s (.endOther 0 false)).isSome) = true := by decide +kernel
example : (run { cfg63 with taskBase := [0, 0] } pre63).any
    (fun s => (step { cfg63 with taskBase := [0, 0] } s (.endOther 0 false)).isSome) = true := by decide +kernel

/-- N1end holds of the instance the replay runs -/
theorem replay_N1end : N1end replay false := N1end_of rfl rfl rfl

end Swarm

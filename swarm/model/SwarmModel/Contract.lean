import SwarmModel.Workers
import SwarmModel.Basic
import SwarmModel.Locks
import SwarmModel.Inbox
import SwarmModel.Workspaces
import SwarmModel.NoWorkLost
import SwarmModel.Fair
import SwarmModel.Gone
import SwarmModel.Real
import SwarmModel.Release
import SwarmModel.End
import SwarmModel.Away
import SwarmModel.Nudge
import SwarmModel.Stay
import SwarmModel.Cut
import SwarmModel.Staff
import SwarmModel.Checkers

/-! The contract (board #25): the theorems a proof about a program that uses the swarm should build on, each restated
here over the model's types (`Cfg`, `State`, `Reachable`, `Run`; `Env.Tools`, `Env.Db`), so a change to one that
breaks this statement breaks the build. Import this module alone (`example/Client.lean` does).

Each is written to `../STYLE.md` (board #86): after the definitions it needs, as ∀, ∃ and named predicates, each proof a
reference. Each says what it guarantees and what it rests on. Its `Fixes` structure lists the `Cfg` switches it takes
as hypotheses, all on in `Cfg`'s defaults but `splitGC`, `perTaskBase`, `recordedWorkspaces`, `bgLives` and `ownAdded`
(main has them; `replay` sets them).
"Env" is which of `Env.lean`'s assumptions it takes, as hypotheses on any `Tools` or `Db`: the model theorems take
none. Nothing is assumed of a machine by axiom (board #68): a client supplies each hypothesis for its machine, by proof
(`Env.consistent` for `Env.ideal`) or as its own hypothesis, and `Trust.lean` shows each one taken here is needed. -/

namespace Swarm.Contract
open Env

/-! ## Safety: every reachable state, any number of agents, tasks, locks and messages -/

/-- Agent `a` is at work: working, or waiting at an hc prompt. -/
def AtWork (s : State) (a : Nat) : Prop := (s.agt a).st = .working ∨ (s.agt a).st = .blocked

theorem atWork_iff (s : State) (a : Nat) : active (s.agt a) = true ↔ AtWork s a := active_spec _

/-- Agent `a` works on task `t`: it is at work and believes it holds `t`. `believes` is what the agent's own commands
told it (a claim adds the task; reading a release, a done or a drop of it removes it), which the board may not agree
with. -/
def WorksOn (s : State) (a t : Nat) : Prop := AtWork s a ∧ t ∈ (s.agt a).believes

/-- S1. No task has two agents working on it. -/
def OneWorkerPerTask (s : State) : Prop := ∀ a b t, WorksOn s a t → WorksOn s b t → a = b

/-- The checker the replay and the counterexamples run, `oneWorker`, checks exactly this. -/
theorem oneWorker_iff (s : State) : oneWorker s = true ↔ OneWorkerPerTask s := oneWorker_spec s

/-- The fixes S1 needs. -/
structure S1Fixes (c : Cfg) : Prop where
  /-- reap reopens a lapsed claim only when its owner is idle -/
  reap_takes_from_idle_only : c.release = .idle
  /-- the user cannot release a task another agent holds, or (board #53) no one may take the released task until its
  ex-owner has read the stop or stopped work; without either, `not_S1_humanRelease` is a run that breaks S1 -/
  user_release_stops_first : c.humanRelease = false ∨ c.stopFirst = true

/-- S1: in every reachable state no task has two agents working on it. Env: none. -/
theorem one_worker_per_task {c : Cfg} (fixes : S1Fixes c) {s : State} (reachable : Reachable c s) :
    OneWorkerPerTask s :=
  (oneWorker_iff s).mp (oneWorker_of_reachable fixes.reap_takes_from_idle_only fixes.user_release_stops_first reachable)

/-- Task `k` is held by agent `a`: `a` owns it, and it is claimed or blocked. -/
def Held (k : Task) (a : Nat) : Prop := k.owner = some a ∧ (k.st = .claimed ∨ k.st = .blocked)

theorem held_iff (k : Task) (a : Nat) : held k a = true ↔ Held k a := held_spec k a

/-- Agent `a` holds task `t` on the board. -/
def HeldBy (s : State) (a t : Nat) : Prop := Held (s.tk t) a

/-- The user released task `t` from agent `o`, which is at work and has not read the stop yet. -/
def Stopped (s : State) (t : Nat) : Prop :=
  ∃ o, (s.tk t).stopTo = some o ∧ AtWork s o ∧ s.cur o < (s.tk t).stopMsg

theorem stopped_iff (s : State) (t : Nat) : stopped s t = true ↔ Stopped s t := stopped_spec s t

/-- S1 at the board: a task an agent at work believes it holds is held by it on the board, or was dropped, or (board
#80) watchd's poll marked it done when its PR merged (`merged`: the merge recorded), which the agent hasn't read yet.
`user_releases_nothing` is the other half of S1's user-release fix. Env: none. -/
theorem believed_task_is_held_dropped_or_merged {c : Cfg} (fixes : S1Fixes c)
    (user_releases_nothing : c.humanRelease = false) {s : State} (reachable : Reachable c s) {a t : Nat}
    (works_on : WorksOn s a t) :
    HeldBy s a t ∨ (s.tk t).st = .dropped ∨ ((s.tk t).st = .done ∧ (s.tk t).merged = true) :=
  (believes_held_of fixes.reap_takes_from_idle_only user_releases_nothing reachable
    ((atWork_iff ..).mpr works_on.1) works_on.2).imp_left ((held_iff ..).mp)

/-- S1 at the board, with H2 and its fix (board #53): a task an agent at work believes it holds is held by it, or was
dropped, or done by watchd's poll (board #80), or the user released it from that agent, which hasn't read the stop yet:
the task is open, its stop names the agent, and no one may take it (`Stopped`). Env: none. -/
theorem believed_task_is_held_dropped_merged_or_stopped {c : Cfg} (fixes : S1Fixes c) {s : State}
    (reachable : Reachable c s) {a t : Nat} (works_on : WorksOn s a t) :
    HeldBy s a t ∨ (s.tk t).st = .dropped ∨ ((s.tk t).st = .done ∧ (s.tk t).merged = true) ∨
      ((s.tk t).st = .opn ∧ Stopped s t) := by
  have active := (atWork_iff ..).mpr works_on.1
  rcases fixes.user_release_stops_first with no_release | stop_first
  · rcases believes_held_of fixes.reap_takes_from_idle_only no_release reachable active works_on.2 with h | h | h
    · exact Or.inl ((held_iff ..).mp h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases believes_held_stop_of fixes.reap_takes_from_idle_only stop_first reachable active works_on.2 with h | h | h | h
    · exact Or.inl ((held_iff ..).mp h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr ⟨h.1, (stopped_iff ..).mp h.2⟩))

/-- S2: the ghost flag `early`, set when a claim happens while a task it is after wasn't done, is never set. -/
def NoEarlyStart (s : State) : Prop := s.early = false

theorem noEarlyStart_iff (s : State) : noEarlyStart s = true ↔ NoEarlyStart s := noEarlyStart_spec s

/-- The fixes S2 needs. -/
structure S2Fixes (c : Cfg) : Prop where
  /-- `task claim` refuses a task while a task it is after isn't done -/
  claim_checks_dependencies : c.claimChecksDeps = true

/-- S2: no task was ever claimed while a task it is after wasn't done. Env: none. -/
theorem no_claim_before_dependencies_done {c : Cfg} (fixes : S2Fixes c) {s : State} (reachable : Reachable c s) :
    NoEarlyStart s :=
  (noEarlyStart_iff s).mp (noEarlyStart_of_reachable fixes.claim_checks_dependencies reachable)

/-- Lock slot `p` is held by agent `a` and has not expired. -/
def LiveLock (s : State) (p a : Nat) : Prop := ∃ l, s.lock[p]? = some l ∧ l.holder = some a ∧ l.exp = false

/-- The fixes S3 needs. -/
structure S3Fixes (c : Cfg) : Prop where
  /-- a lock is refused while another agent's live lock overlaps it -/
  lock_checks_overlap : c.lockOverlap = true
  /-- a lock pattern is a file, a glob or a directory, and nothing else (board #26) -/
  lock_patterns_are_files_globs_or_directories : c.lockForms = true

/-- S3, as files: two live locks of different agents never both cover one path. Env: none. -/
theorem no_path_covered_by_two_agents_locks {c : Cfg} (fixes : S3Fixes c) {s : State} (reachable : Reachable c s)
    {p q a b : Nat} (p_held : LiveLock s p a) (q_held : LiveLock s q b) (different_locks : p ≠ q)
    (different_agents : a ≠ b) {path : String} (is_path : Glob.Bytes path.toList) :
    ¬ (covers c path (c.pat p) = true ∧ covers c path (c.pat q) = true) := by
  obtain ⟨l, hp, ha, he1⟩ := p_held
  obtain ⟨m, hq, hb, he2⟩ := q_held
  exact noSharedFile_of_reachable fixes.lock_checks_overlap fixes.lock_patterns_are_files_globs_or_directories
    reachable hp hq different_locks ha hb different_agents he1 he2 path is_path

/-- S4. Per agent: what was shown to it is shown once and in order, and its cursor has passed a message addressed to
it only if it was shown. (`seen` is the ghost list of ids shown; `start` the log's length when the agent was spawned.) -/
structure InboxExact (s : State) : Prop where
  /-- no message is shown twice, and they are shown in order -/
  shown_once_in_order : ∀ a, a < s.ag.length → (s.seen.getD a []).Pairwise (· < ·)
  /-- every message addressed to the agent, from another, that the cursor passed since the spawn was shown -/
  cursor_passes_only_shown : ∀ a, a < s.ag.length → ∀ i, s.start.getD a 0 < i → i ≤ s.cur a →
    (s.msg i).to = a → (s.msg i).frm ≠ some a → i ∈ s.seen.getD a []

theorem inboxExact_iff (s : State) : inboxExact s = true ↔ InboxExact s :=
  (inboxExact_spec s).trans
    ⟨fun h => ⟨fun a ha => (h a ha).1, fun a ha => (h a ha).2⟩, fun h a ha => ⟨h.1 a ha, h.2 a ha⟩⟩

/-- The fixes S4 needs. -/
structure S4Fixes (c : Cfg) : Prop where
  /-- delivery advances the cursor only by a compare-and-set, so two deliveries never show a message twice -/
  delivery_is_compare_and_set : c.deliverCas = true

/-- S4: no message is shown twice, and no cursor passes a message it didn't show. Env: none. -/
theorem inbox_shows_each_message_once {c : Cfg} (fixes : S4Fixes c) {s : State} (reachable : Reachable c s) :
    InboxExact s :=
  (inboxExact_iff s).mp (inboxExact_of_reachable fixes.delivery_is_compare_and_set reachable)

/-- S5. Every done task has evidence. -/
def DoneHasEvidence (s : State) : Prop := ∀ k ∈ s.task, k.st = .done → k.ev = true

theorem doneHasEvidence_iff (s : State) : doneHasEvidence s = true ↔ DoneHasEvidence s := doneHasEvidence_spec s

/-- The fixes S5 needs. -/
structure S5Fixes (c : Cfg) : Prop where
  /-- `task done` refuses an empty evidence (PR #113) -/
  done_needs_evidence : c.evidenceRequired = true

/-- S5: every done task has evidence. Env: none. -/
theorem done_task_has_evidence {c : Cfg} (fixes : S5Fixes c) {s : State} (reachable : Reachable c s) :
    DoneHasEvidence s :=
  (doneHasEvidence_iff s).mp (doneHasEvidence_of_reachable fixes.done_needs_evidence reachable)

/-- Worktree `w` is in use: a live agent has it as its worktree, or conflict's `wt_map` picks it for that agent. -/
def InUse (c : Cfg) (s : State) (w : Nat) : Prop :=
  ∃ b ∈ c.agents, (s.agt b).live = true ∧ ((s.agt b).wt = some w ∨ wtmap c s b = some w)

/-- W1, of a step from `s` to the git state `g'`: a worktree it removes was clean, in no one's use, had no process
inside and its HEAD on a protected ref; a branch it deletes is no protected ref and its tip was on one. -/
structure GcOk (c : Cfg) (s : State) (g' : Git) : Prop where
  /-- a removed worktree was clean, unattached, empty of processes and its HEAD on a protected ref -/
  removed_worktree_was_landed : ∀ w ∈ c.wtIds, (s.git.wt w).on = true → (g'.wt w).on = false →
    (s.git.wt w).dirty = false ∧ ¬ InUse c s w ∧ (s.git.wt w).proc = false ∧ s.git.safe c (s.git.wt w).head = true
  /-- a deleted branch is no protected ref, and its tip was on one -/
  deleted_branch_was_landed : ∀ b < s.git.brs.length, (∃ k, s.git.tip b = some k) → g'.tip b = none →
    c.nbases ≤ b ∧ s.git.safe c (s.git.tipOf b) = true

theorem gcOk_iff (c : Cfg) (s : State) (g' : Git) : gcOk c s g' = true ↔ GcOk c s g' :=
  (gcOk_spec c s g').trans ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

/-- W1: every step of every reachable state removes a worktree or a branch only if it was landed. -/
def GcRemovesOnlyLanded (c : Cfg) : Prop :=
  ∀ s act s', Reachable c s → step c s act = some s' → GcOk c s s'.git

/-- The fix W1 needs. -/
structure W1Fixes (c : Cfg) : Prop where
  /-- ending an agent removes no worktree: workspace GC alone does, by reachability from a protected ref (board #4) -/
  gc_alone_removes_worktrees : c.splitGC = true

/-- W1: a step removes a worktree only if it was clean, unattached, had no process inside and its HEAD on a protected
ref, and deletes a branch only if it is no protected ref and its tip was on one. Env: none (`sweep_gate_implies_w1_premise` is the same
gate on the tools' answers). -/
theorem workspace_gc_removes_only_landed {c : Cfg} (fixes : W1Fixes c) : GcRemovesOnlyLanded c :=
  fun _ act _ reachable steps => (gcOk_iff ..).mp (W1_of c fixes.gc_alone_removes_worktrees _ act _ reachable steps)

/-- Worktree `w` has work that is not landed for agent `a`: it is there, and it is dirty or its HEAD is reachable from
no base of a task `a` owns (main, if it owns none). -/
def Unlanded (c : Cfg) (s : State) (a w : Nat) : Prop := s.git.landedIn (abases c s a) w = false

/-- Agent `a` holds work: its row is live, and a background job of its own runs and has not stalled (a sleep loop or no
CPU for JOB_HUNG past its nudge, board #125), or the worktree it works in is
unlanded, or one it added is. -/
def HoldsWork (c : Cfg) (s : State) (a : Nat) : Prop :=
  (s.agt a).live = true ∧
    ((s.agt a).bg = true ∧ (s.agt a).stalled = false
      ∨ (∃ w, wtmap c s a = some w ∧ Unlanded c s a w)
      ∨ ∃ w gen, (w, gen) ∈ (s.agt a).own ∧ owns s a w = true ∧ Unlanded c s a w)

/-- `s'` has agent `a` as `s` had it (not ended, its job, its worktrees), but for the pool ids a digest told it of. -/
def KeptBy (s s' : State) (a : Nat) : Prop := { s'.agt a with told := [] } = { s.agt a with told := [] }

theorem holdsWork_iff (c : Cfg) (s : State) (a : Nat) : holdsWork c s a = true ↔ HoldsWork c s a := holdsWork_spec c s a
theorem keptBy_iff (s s' : State) (a : Nat) : keptBy s s' a = true ↔ KeptBy s s' a := keptBy_spec s s' a

/-- N1. watchd never discards work that isn't landed. `tickOf c s` is the state after watchd's tick from `s`, and
`reapLocks (reapTasks c s)` the state after the tick's first pass, reap. -/
structure NoWorkLost (c : Cfg) : Prop where
  /-- the tick leaves alone every agent that holds work once reap has run -/
  tick_keeps_agent_holding_work : ∀ s a, Reachable c s →
    HoldsWork c (reapLocks (reapTasks c s)) a → KeptBy s (tickOf c s) a
  /-- the tick takes no claim from a live owner whose background job runs -/
  tick_keeps_claim_while_job_runs : ∀ s t owner, Reachable c s →
    (s.tk t).st = .claimed → (s.tk t).owner = some owner → (s.agt owner).live = true → (s.agt owner).bg = true →
    ((tickOf c s).tk t).owner = some owner
  /-- an agent may claim back a task reap took from it: the 350k fence does not refuse it -/
  reaped_task_can_be_claimed_back : ∀ s a t, Reachable c s → (s.tk t).reaped = some a → fenced c s a t = false
  /-- workspace GC removes only what is clean and on a protected ref (W1, above) -/
  gc_removes_only_landed : GcRemovesOnlyLanded c

/-- `N1`, the form the counterexamples refute, says the same. -/
theorem noWorkLost_iff (c : Cfg) : N1 c ↔ NoWorkLost c :=
  ⟨fun h => ⟨fun s a r w => (keptBy_iff ..).mp (h.1 s a r ((holdsWork_iff ..).mpr w)), h.2.1, h.2.2.1,
      fun s act s' r st => (gcOk_iff ..).mp (h.2.2.2 s act s' r st)⟩,
   fun h => ⟨fun s a r w => (keptBy_iff ..).mpr (h.1 s a r ((holdsWork_iff ..).mp w)), h.2, h.3,
      fun s act s' r st => (gcOk_iff ..).mpr (h.4 s act s' r st)⟩⟩

/-- The fixes about what counts as landed, shared by N1 and `swarm end` (H1). -/
structure LandedFixes (c : Cfg) : Prop where
  /-- lifecycle keeps an agent while any worktree it owns is unlanded, not only the one it works in (PR #123) -/
  lifecycle_checks_all_worktrees : c.allWts = true
  /-- lifecycle also counts the worktrees a spawned agent added itself (board #15) -/
  lifecycle_counts_added_worktrees : c.ownAdded = true
  /-- "landed" means on a base of a task the agent owns, not on main alone (sw-bases, board #3) -/
  landed_is_per_task_base : c.perTaskBase = true

/-- The fixes N1 needs but the fence's, which a tick an error ends partway needs too. -/
structure CutTickFixes (c : Cfg) : Prop extends W1Fixes c, LandedFixes c where
  /-- reap reopens a lapsed claim only when its owner is idle -/
  reap_takes_from_idle_only : c.release = .idle
  /-- reap keeps a lapsed claim whose idle owner has a background job running (PR #121) -/
  reap_keeps_claim_while_job_runs : c.bgKeeps = true
  /-- lifecycle keeps an idle agent while its background job runs (board #15) -/
  lifecycle_keeps_agent_while_job_runs : c.bgLives = true

/-- The fixes N1 needs; each is needed (`not_N1_bgKeeps`, `not_N1_retake`, `not_N1_allWts`, `not_N1_bgLives`,
`not_N1_ownAdded` are runs that break it without). -/
structure N1Fixes (c : Cfg) : Prop extends CutTickFixes c where
  /-- the 350k fence on `task claim` lets a big agent take back what reap took from it (PR #121) -/
  fence_allows_claim_back : c.retake = true

theorem N1Fixes.n1 {c : Cfg} (fixes : N1Fixes c) : N1 c :=
  N1_of c fixes.reap_takes_from_idle_only fixes.reap_keeps_claim_while_job_runs fixes.fence_allows_claim_back
    fixes.lifecycle_checks_all_worktrees fixes.lifecycle_keeps_agent_while_job_runs
    fixes.lifecycle_counts_added_worktrees fixes.landed_is_per_task_base fixes.gc_alone_removes_worktrees

/-- N1: watchd never discards work that isn't landed. Env: none. -/
theorem no_work_lost {c : Cfg} (fixes : N1Fixes c) : NoWorkLost c := (noWorkLost_iff c).mp fixes.n1

/-- N1, W1 and W2 of a tick an error ends partway (`tickCut c k s`: the tick with each pass cut where `k` says, board
#84; `Reachable.cut` makes every theorem above hold of what it leaves). -/
structure NoWorkLostWhenCut (c : Cfg) : Prop where
  /-- the cut tick leaves alone every agent that holds work once its reap has run -/
  cut_tick_keeps_agent_holding_work : ∀ s k a, Reachable c s →
    HoldsWork c (reapCut c k.reap s) a → KeptBy s (tickCut c k s) a
  /-- the cut tick takes no claim from a live owner whose background job runs -/
  cut_tick_keeps_claim_while_job_runs : ∀ s k t owner, Reachable c s →
    (s.tk t).st = .claimed → (s.tk t).owner = some owner → (s.agt owner).live = true → (s.agt owner).bg = true →
    ((tickCut c k s).tk t).owner = some owner
  /-- workspace GC of the cut tick removes only what is landed (W1) -/
  cut_tick_gc_removes_only_landed : ∀ s k, Reachable c s → GcOk c s (tickCut c k s).git
  /-- ending an agent in the cut tick removes no worktree and deletes no branch (W2) -/
  cut_tick_end_removes_no_worktree : ∀ s k, Reachable c s → cutSweep c k s true = cutSweep c k s false

theorem noWorkLostWhenCut_iff (c : Cfg) : N1cut c ↔ NoWorkLostWhenCut c :=
  ⟨fun h => ⟨fun s k a r w => (keptBy_iff ..).mp (h.1 s k a r ((holdsWork_iff ..).mpr w)), h.2.1,
      fun s k r => (gcOk_iff ..).mp (h.2.2.1 s k r), h.2.2.2⟩,
   fun h => ⟨fun s k a r w => (keptBy_iff ..).mpr (h.1 s k a r ((holdsWork_iff ..).mp w)), h.2,
      fun s k r => (gcOk_iff ..).mpr (h.3 s k r), h.4⟩⟩

/-- N1, W1 and W2 of a tick an error ends partway. Env: none. -/
theorem no_work_lost_when_tick_cut {c : Cfg} (fixes : CutTickFixes c) : NoWorkLostWhenCut c :=
  (noWorkLostWhenCut_iff c).mp
    (N1cut_of c fixes.reap_takes_from_idle_only fixes.reap_keeps_claim_while_job_runs fixes.lifecycle_checks_all_worktrees
      fixes.lifecycle_keeps_agent_while_job_runs fixes.lifecycle_counts_added_worktrees fixes.landed_is_per_task_base
      fixes.gc_alone_removes_worktrees)

/-- The fix a failed pass needs. -/
structure PassGuardFixes (c : Cfg) : Prop where
  /-- each pass of watchd's tick runs under its own `pcall` (board #84) -/
  each_pass_guarded : c.passGuard = true

/-- A failed pass stops no other pass of the tick (board #84): an error in any one pass alone, at any of its units, is a
cut the tick may make. Env: none. -/
theorem failed_pass_stops_no_other_pass {c : Cfg} (fixes : PassGuardFixes c) :
    ∀ failed_at : Option Nat, Cut.ok c ⟨failed_at, none, none, none⟩ ∧ Cut.ok c ⟨none, failed_at, none, none⟩ ∧
      Cut.ok c ⟨none, none, failed_at, none⟩ ∧ Cut.ok c ⟨none, none, none, failed_at⟩ :=
  passesIndep_of fixes.each_pass_guarded

/-! ## Liveness: over fair runs (`Run.Fair`: every action enabled infinitely often in `fair` is taken) -/

/-- Task `t` is claimed by agent `a`, which is idle. -/
def IdleClaim (s : State) (a t : Nat) : Prop := ((s.tk t).st = .claimed ∧ (s.tk t).owner = some a) ∧ (s.agt a).st = .idle

theorem idleClaim_iff (s : State) (a t : Nat) : idleClaim s a t = true ↔ IdleClaim s a t := idleClaim_spec s a t

/-- The fix L2 needs. -/
structure L2Fixes (c : Cfg) : Prop where
  /-- reap reopens a lapsed claim and leaves its owner's row alone, rather than ending the agent -/
  reap_does_not_end_owner : c.release ≠ .ended

/-- L2: a claimed task whose owner is idle is eventually done or open again, or its owner back at work, while no agent
starts a background job or dies. Its other conditions are not fixes: commands are modelled as one step each, and watchd
runs. Env: none. -/
theorem idle_claim_ends {c : Cfg} (fixes : L2Fixes c) (commands_are_one_step : c.racy = false)
    (watchd_runs : c.watchd = true) {a t : Nat} (is_agent : a ∈ c.agents) (is_task : t ∈ c.tasks) (r : Run c)
    (fair : r.Fair) {n : Nat} (no_job_starts_or_death : ∀ k, n ≤ k → ∀ b, r.act k ≠ .bgStart b ∧ r.act k ≠ .die b)
    (no_job_at_n : ((r.st n).agt a).bg = false) (alive_at_n : ((r.st n).agt a).dead = false)
    (idle_claim : IdleClaim (r.st n) a t) : ∃ m, n ≤ m ∧ ¬ IdleClaim (r.st m) a t :=
  (idleClaim_leads_to commands_are_one_step fixes.reap_does_not_end_owner watchd_runs is_agent is_task r fair
    no_job_starts_or_death no_job_at_n alive_at_n ((idleClaim_iff ..).mpr idle_claim)).imp
    fun _ h => ⟨h.1, fun g => Bool.eq_false_iff.mp h.2 ((idleClaim_iff ..).mpr g)⟩

/-- Agent `a`'s row outlives its terminal: the terminal is gone, and the row still reads as live (so its claims and
locks are still held). -/
def RowOutlivesTerminal (s : State) (a : Nat) : Prop := (s.agt a).live = true ∧ (s.agt a).dead = true

theorem deadLive_iff (s : State) (a : Nat) : deadLive s a = true ↔ RowOutlivesTerminal s a := deadLive_spec s a

/-- L4: on a fair run, a row that outlives its terminal does not stay so: watchd's reap ends it (its claims reopened,
its locks freed), or something else does first. Its conditions are not fixes, so each is its own hypothesis: commands
are modelled as one step each (`racy` off: not proved of the split read-then-write model), watchd runs, `hc ls`
answers, and the row has an hc address. The last three are needed (findings #14, #15). Env: none
(`reap_reads_gone_iff_terminal_gone` is `hc ls` telling it). -/
theorem gone_terminal_row_is_ended {c : Cfg} (commands_are_one_step : c.racy = false) (watchd_runs : c.watchd = true)
    (hc_ls_answers : c.hcSees = true) {a : Nat} (is_agent : a ∈ c.agents) (has_hc_address : a ∉ c.unbound)
    (r : Run c) (fair : r.Fair) {n : Nat} (reachable : Reachable c (r.st n))
    (outlives : RowOutlivesTerminal (r.st n) a) : ∃ m, n ≤ m ∧ ¬ RowOutlivesTerminal (r.st m) a :=
  (deadLive_leads_to commands_are_one_step watchd_runs hc_ls_answers is_agent (by simpa using has_hc_address) r fair
    reachable ((deadLive_iff ..).mpr outlives)).imp fun _ h => ⟨h.1, fun g => Bool.eq_false_iff.mp h.2 ((deadLive_iff ..).mpr g)⟩

/-- H2: after the user's or the communicator's release of a task another holds, its ex-owner is sent a stop and does
not keep at work unaware of it forever: it reads it, stops being at work, or its terminal is gone (which
`gone_terminal_row_is_ended` ends). Env: none. -/
theorem released_owner_reads_stop {c : Cfg} (r : Run c) (fair : r.Fair) {n t : Nat} (reachable : Reachable c (r.st n))
    (releases : r.act n = .releaseOther t) :
    ∃ owner i, HeldBy (r.st n) owner t ∧ ((r.st (n + 1)).msg i).kind = .released ∧ ((r.st (n + 1)).msg i).task = t ∧
      ∃ m, n + 1 ≤ m ∧ (¬ AtWork (r.st m) owner ∨ ((r.st m).agt owner).dead = true ∨ i ≤ (r.st m).cur owner) := by
  obtain ⟨o, i, held, kind, task, m, hm, h⟩ := released_reads r fair reachable releases
  refine ⟨o, i, (held_iff ..).mp held, kind, task, m, hm, h.imp (fun h works => ?_) id⟩
  have := (atWork_iff ..).mpr works
  simp_all

/-- Agent `a`'s unlanded work, as lifecycle reads it: in the worktree `wt_map` picks, or in one it owns (those it added
too, if `ownAdded`), or in its recorded worktree against the bases of its tasks. -/
def LifecycleUnlanded (c : Cfg) (s : State) (a : Nat) : Prop :=
  (∃ w, wtmap c s a = some w ∧ landedC c s.git (abases c s a) w = false) ∨
  (c.allWts = true ∧ ((s.agt a).recorded = false ∨ c.ownAdded = true) ∧
    ∃ p ∈ (s.agt a).own, owns s a p.1 = true ∧ landedC c s.git (abases c s a) p.1 = false) ∨
  ∃ k, (s.agt a).rhead = some k ∧ landedK c s.git ((s.agt a).rbase :: abases c s a) k = false

theorem unlanded_iff (c : Cfg) (s : State) (a : Nat) : unlanded c s a = true ↔ LifecycleUnlanded c s a :=
  unlanded_spec c s a

/-- `swarm end A` is allowed: `A` is idle, holds no stay, task or lock, runs no background job and has nothing unlanded. -/
def Endable (c : Cfg) (s : State) (a : Nat) : Prop :=
  (s.agt a).st = .idle ∧ (s.agt a).stay = false ∧ (¬ ∃ k ∈ s.task, Held k a) ∧ (¬ ∃ l ∈ s.lock, l.holder = some a) ∧
    (s.agt a).bg = false ∧ ¬ LifecycleUnlanded c s a

theorem endable_iff (c : Cfg) (s : State) (a : Nat) : endable c s a = true ↔ Endable c s a := endable_spec c s a

/-- H1: `swarm end A` by the user or the communicator without --force never ends an agent that holds work (a background
job running, or work off its tasks' bases in a worktree it works in or owns): its check is lifecycle's but the 2 min.
`--force` does (`not_N1end_force`). Env: none. -/
theorem end_refuses_agent_holding_work {c : Cfg} (fixes : LandedFixes c) {s s' : State} {a : Nat}
    (reachable : Reachable c s) (ends : step c s (.endOther a false) = some s') : ¬ HoldsWork c s a :=
  fun holds => Bool.eq_false_iff.mp
    (N1end_of fixes.lifecycle_checks_all_worktrees fixes.lifecycle_counts_added_worktrees fixes.landed_is_per_task_base
      s s' a reachable ends) ((holdsWork_iff ..).mpr holds)

/-- `swarm end A` without --force ends `A`'s row and changes nothing else. -/
structure EndChangesOnlyRow (c : Cfg) (s s' : State) (a : Nat) : Prop where
  /-- it is refused unless `A` is endable -/
  only_endable : Endable c s a
  tasks_unchanged : s'.task = s.task
  locks_unchanged : s'.lock = s.lock
  messages_unchanged : s'.log = s.log
  cursors_unchanged : s'.cursor = s.cursor
  git_unchanged : s'.git = s.git
  row_ended : a < s.ag.length → (s'.agt a).st = .ended
  other_agents_unchanged : ∀ b, b ≠ a → s'.agt b = s.agt b

/-- H1: `swarm end A` without --force changes nothing but A's row: A ended, no task, lock, message, cursor, git ref or
other agent changed. Env: none. -/
theorem end_changes_only_the_row {c : Cfg} {s s' : State} {a : Nat} (ends : step c s (.endOther a false) = some s') :
    EndChangesOnlyRow c s s' a := by
  obtain ⟨e, t, l, m, cu, g, r, o⟩ := endOther_spec ends
  exact ⟨(endable_iff ..).mp e, t, l, m, cu, g, r, o⟩

/-- Task `t`'s latest question was told: of its question events (`task block`, task-blocked) the last is a
task-blocked, and no question event of `t` follows it. -/
def Told (evs : List Ev) (t : Nat) : Prop :=
  ∃ before after hc, evs = before ++ Ev.tblocked t hc :: after ∧ ∀ e ∈ after, e ≠ .block t ∧ ∀ hc', e ≠ .tblocked t hc'

theorem toldAfter_iff (evs : List Ev) (t : Nat) : toldAfter evs t = true ↔ Told evs t := toldAfter_spec evs t

/-- The fix Q1 needs. -/
structure Q1Fixes (c : Cfg) : Prop where
  /-- the tick tells again a blocked task whose latest question was not told (board #47) -/
  tick_retells_blocked_tasks : c.renotify = true

/-- Q1 (board #47): after a tick every blocked task's latest question was told. Env: none. -/
theorem blocked_task_question_is_told {c : Cfg} (fixes : Q1Fixes c) :
    ∀ s t, t ∈ c.tasks → ((tickOf c s).tk t).st = .blocked → Told (tickOf c s).evs t :=
  fun s t is_task blocked => (toldAfter_iff ..).mp (Q1_of fixes.tick_retells_blocked_tasks s t is_task blocked)

/-- The fix A2's quiet half needs. -/
structure AwayQuietFixes (c : Cfg) : Prop where
  /-- a block notice is sent quietly while the user is away -/
  notice_quiet_while_away : c.awayQuiet = true

/-- A2 (board #47): a block notice is urgent exactly when the user is not away. Env: none. -/
theorem block_notice_urgent_iff_user_not_away {c : Cfg} (fixes : AwayQuietFixes c) :
    ∀ s act s', step c s act = some s' → ∀ notice ∈ s'.cbox.drop s.cbox.length, notice.kind = .blocked →
      (notice.urgent = true ↔ s.away = none) :=
  A2quiet_of fixes.notice_quiet_while_away

/-- The fix A2's live half needs. -/
structure BackTellsFixes (c : Cfg) : Prop where
  /-- `--back` tells the communicator everything it was sent while away -/
  back_tells_unread : c.backTells = true

/-- A2 (board #47): on a run fair to the communicator's waiter, all it was sent before `--back` is read. Env: none. -/
theorem notices_before_back_are_read {c : Cfg} (fixes : BackTellsFixes c) :
    ∀ r : Run c, r.CommsFair → ∀ m i, r.act m = .back → i < (r.st m).cbox.length → ∃ k, i < (r.st k).ccur :=
  A2live_of fixes.back_tells_unread

/-- A3 (board #47): the away flag changes nothing the tick does but the notices' urgency. Env: none. -/
theorem away_changes_only_urgency (c : Cfg) (s : State) (away : Option Nat) :
    blind (tickOf c (withAway s away)) = blind (tickOf c s) := A3 c s away

/-- What `swarm nudge` of `line` into terminal `terminal` of the world `w` does. -/
structure NudgeTypesOnly (t : Tools) (s s' : State) (w : t.World) (terminal : Nat) (line : String) : Prop where
  state_unchanged : s' = s
  line_typed_into_terminal : t.typed (t.hcSend w terminal line) terminal = t.typed w terminal ++ [line]
  other_terminals_untouched : ∀ other, other ≠ terminal → t.typed (t.hcSend w terminal line) other = t.typed w other
  no_terminal_started_or_ended : ∀ other, t.termLive (t.hcSend w terminal line) other = t.termLive w other
  repo_durable_state_unchanged : Git.durable (t.git (t.hcSend w terminal line)) = Git.durable (t.git w)

example (t : Tools) : HcSendTargets t = ∀ w h l, t.termLive w h = true →
    t.typed (t.hcSend w h l) h = t.typed w h ++ [l] ∧ (∀ h', h' ≠ h → t.typed (t.hcSend w h l) h' = t.typed w h') ∧
    (∀ h', t.termLive (t.hcSend w h l) h' = t.termLive w h') ∧ Git.durable (t.git (t.hcSend w h l)) = Git.durable (t.git w) := rfl

/-- N1' (board #50): `swarm nudge` changes no task, claim, lock, lease, message or cursor; it types its line into the
nudged agent's terminal only, starts or ends no terminal, and leaves the repo's durable state. Env: `HcSendTargets`. -/
theorem nudge_types_into_one_terminal {t : Tools} (hc_send_targets : HcSendTargets t) {c : Cfg} {s s' : State} {a : Nat}
    (nudges : step c s (.hnudge a) = some s') {w : t.World} {terminal : Nat} (terminal_live : t.termLive w terminal = true)
    (line : String) : NudgeTypesOnly t s s' w terminal line := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := Tools.N1' hc_send_targets nudges terminal_live line
  exact ⟨h1, h2, h3, h4, h5⟩

/-- A stayer (board #79): the tick keeps its row (but for the pool ids a digest told it of), and `swarm end` without
--force refuses it. -/
structure StayerKept (c : Cfg) (s : State) (a : Nat) : Prop where
  tick_keeps_row : KeptBy s (tickOf c s) a
  end_refuses : step c s (.endOther a false) = none

/-- Stays (board #79): the tick keeps a live stayer's row, and `swarm end` without --force refuses it. Env: none. -/
theorem stayer_is_kept {c : Cfg} {s : State} {a : Nat} (stays : (s.agt a).stay = true) (live : (s.agt a).live = true) :
    StayerKept c s a :=
  ⟨tick_keeps_stayer stays live, endOther_stay stays⟩

/-- `swarm stay --end A` changes `A`'s stay alone, and the tick after it keeps `A` while `A` holds work. -/
structure EndStayChangesOnlyStay (c : Cfg) (s s' : State) (a : Nat) : Prop where
  /-- no task, claim, lease, lock, message, cursor, git ref or event changes: only the agents' rows -/
  nothing_but_agents_changes : s' = { s with ag := s'.ag }
  agent_count_unchanged : s'.ag.length = s.ag.length
  only_the_stay_changes : ∀ b, s'.agt b = if b = a then { s.agt a with stay := false } else s.agt b
  tick_keeps_agent_holding_work : HoldsWork c (reapLocks (reapTasks c s')) a → KeptBy s' (tickOf c s') a

/-- Stays (board #48): `swarm stay --end A` by the user or the communicator changes A's stay alone, and the tick after
it keeps A while A holds work. Env: none. -/
theorem end_stay_changes_only_the_stay {c : Cfg} (fixes : N1Fixes c) {s s' : State} {a : Nat}
    (reachable : Reachable c s) (ends_stay : step c s (.endStay a) = some s') : EndStayChangesOnlyStay c s s' a :=
  have frame := endStay_frame ends_stay
  ⟨frame.1, frame.2.1, frame.2.2, fun holds =>
    (keptBy_iff ..).mp (endStay_N1 fixes.n1 reachable ends_stay ((holdsWork_iff ..).mpr holds))⟩

/-- Stays (board #79): `--back`'s digest lists a slot as hung exactly when its agent hung since away and did not end
since. Env: none. -/
theorem digest_lists_slot_iff_hung_since_away (c : Cfg) (s : State) (since a : Nat) :
    a ∈ (digestOf c s since).hung ↔
      a < c.nagents ∧ ∃ before after, s.evs.drop since = before ++ .hung a :: after ∧ Ev.ended a ∉ after :=
  digest_hung c s since a

/-! ## Several swarms and their watchds (`CCfg`, `World`, `cstep`: `Comms.lean`) -/

/-- Watchd process `p` is mid-tick of swarm `i`: it holds the swarm's tick lease (meta.watchd_tick) and runs. -/
def MidTick (w : World) (i p : Nat) : Prop := w.tkOf i = some p ∧ w.alive p = true

theorem midTick_iff (w : World) (i p : Nat) : midTick w i p = true ↔ MidTick w i p := midTick_spec w i p

/-- Step `act` runs watchd `p`'s tick of swarm `i`: `tick i` runs the tick of the watchd the swarm's record names,
`tend p` the rest of `p`'s own after a takeover. -/
def RunsTick (w : World) (act : CAction) (i p : Nat) : Prop := tickOfStep w act = some (i, p)

/-- R1 (a'), board #71. No two ticks of a swarm overlap, a takeover's included. In the Lua a tick runs from its claim
of the tick lease to its release, and a `--restart` can land in between. -/
structure TicksNeverOverlap (c : CCfg) : Prop where
  /-- a step that runs a watchd's tick of a swarm finds no other watchd mid-tick of it -/
  tick_finds_no_other_mid_tick : ∀ w w' act i p q, cstep c w act = some w' →
    RunsTick w act i p → MidTick w i q → q = p
  /-- a watchd mid-tick keeps the lease until a step runs its tick -/
  mid_tick_keeps_lease : ∀ w w' act i p, cstep c w act = some w' →
    MidTick w i p → ¬ RunsTick w act i p → w'.tkOf i = some p

/-- `R1a'`, the form `Restart.lean` proves, says the same. -/
theorem ticksNeverOverlap_iff (c : CCfg) : R1a' c ↔ TicksNeverOverlap c :=
  ⟨fun h => ⟨fun w w' act i p q st rt mt => (h w w' act st).1 i p q rt ((midTick_iff ..).mpr mt),
             fun w w' act i p st mt nr => (h w w' act st).2 i p ((midTick_iff ..).mpr mt) nr⟩,
   fun h w w' act st => ⟨fun i p q rt mt => h.1 w w' act i p q st rt ((midTick_iff ..).mp mt),
                         fun i p mt nr => h.2 w w' act i p st ((midTick_iff ..).mp mt) nr⟩⟩

/-- R1 (a'): no two ticks of a swarm overlap, of every step from any world (reachable or not). Switches: none.
Env: none. -/
theorem ticks_never_overlap (c : CCfg) : TicksNeverOverlap c := (ticksNeverOverlap_iff c).mp (R1a'_of c)

/-! ## Staffing order (board #91): which task an auto-spawn launch is for

`FWorld` is the instance's `State` with each task's rank (`rk`: red-main or not, its priority), auto-spawn's loop and
its meta rows (`backoff`, `halt`); `fstep` runs the instance's actions between the launches of one tick. -/

/-- Task `h` is before task `l` in the pool's order: a red-main task first, then the lower priority number, then the
lower id. -/
def Outranks (w : FWorld) (h l : Nat) : Prop :=
  ((w.rk h).red = true ∧ (w.rk l).red = false) ∨
    ((w.rk h).red = (w.rk l).red ∧
      ((w.rk h).priority < (w.rk l).priority ∨ ((w.rk h).priority = (w.rk l).priority ∧ h < l)))

theorem outranks_iff (w : FWorld) (h l : Nat) : before w h l = true ↔ Outranks w h l := before_spec w h l

/-- Auto-spawn may staff task `t`: it is in the pool (open, every dependency done, no stop pending) and auto-spawn has
not given up on it (`spawn_halt`, after five failed launches in a row). -/
def Staffable (c : FCfg) (w : FWorld) (t : Nat) : Prop := t ∈ pool c.sw w.s ∧ w.halt ≠ some t

/-- The step from `w` to `w'` is an auto-spawn launch for task `l`. -/
def Launches (c : FCfg) (w w' : FWorld) (l : Nat) : Prop := fstep c w (.launch l) = some w'

/-- The step from `w` to `w'` is agent `a`'s `task done` of task `x`. -/
def Finishes (c : FCfg) (w w' : FWorld) (a x : Nat) : Prop := ∃ evidence, fstep c w (.sw (.done a x evidence)) = some w'

/-- The step from `w` to `w'` is agent `a`'s `task release` of task `x`. -/
def Releases (c : FCfg) (w w' : FWorld) (a x : Nat) : Prop := fstep c w (.sw (.release a x)) = some w'

/-- Open task `h` waits on `x` and nothing else: no stop is pending on it and each of its other dependencies is
done. -/
def WaitsOnlyOn (c : FCfg) (s : State) (h x : Nat) : Prop :=
  h ∈ c.sw.tasks ∧ (s.tk h).st = .opn ∧ ¬ Stopped s h ∧ x ∈ (s.tk h).deps ∧
    ∀ d, d ∈ (s.tk h).deps → d = x ∨ (s.tk d).st = .done

/-- F1's fix, a switch of our code. -/
structure StaffingFixes (c : FCfg) : Prop where
  /-- auto_spawn reads the pool again before each launch, and the launch's claim checks in its own transaction that
  its task still heads it (board #91); before, every launch of a tick walked the pool lifecycle read at its top -/
  each_launch_reads_the_pool : c.freshPool = true

/-- F1 (board #91), part by part. -/
structure StaffsFreedTaskFirst (c : FCfg) : Prop where
  /-- a task's last dependency going done puts it in the pool at that step -/
  done_frees_the_dependent : ∀ w w' a x h, Finishes c w w' a x → WaitsOnlyOn c w.s h x → h ∈ pool c.sw w'.s
  /-- a release of the dependency does not: the dependent stays out of the pool -/
  release_frees_nothing : ∀ w w' a x h, Releases c w w' a x → x ∈ (w.s.tk h).deps → h ∉ pool c.sw w'.s
  /-- a launch is for a staffable task -/
  launch_is_for_a_staffable_task : ∀ w w' l, Launches c w w' l → Staffable c w l
  /-- a launch is for `h`, or for a task before it, whenever `h` is in the pool and not given up on: nothing staffable
  is passed over for a task after it -/
  launch_passes_over_no_staffable_task : ∀ w w' l h, Launches c w w' l → h ∈ pool c.sw w.s →
    (not_given_up_on : w.halt ≠ some h) → l = h ∨ Outranks w l h
  /-- while a backoff holds (a launch failed) there is no launch at all -/
  no_launch_in_a_backoff : ∀ w w' l, Launches c w w' l → w.backoff = false

/-- F1. Once a task's last dependency is done it is in the pool, and from then on every auto-spawn launch is for it or
for a task before it in the pool's order (red main, priority, id), as long as it is still in the pool and auto-spawn has
not given up on it: of every step from any world, so whatever ran between lifecycle's read of the pool and the launch.
A release frees nothing, and a backoff launches nothing. Not said: that a launch happens (the auto-spawn number, free
memory, a backoff and a reusable idle agent each hold it back; with a reusable agent alive watchd spawns no one and that
agent picks a task itself). Without the fix it fails (finding #37, `not_F1`). Env: none. -/
theorem freed_task_is_staffed_first {c : FCfg} (fixes : StaffingFixes c) : StaffsFreedTaskFirst c :=
  ⟨fun _ _ _ _ _ finishes waits => finishes.elim fun _ done =>
      done_frees done waits.1 waits.2.1 (fun e => waits.2.2.1 ((stopped_iff ..).mp e)) waits.2.2.2.2,
   fun _ _ _ _ _ releases waits => release_waits releases waits,
   fun _ _ _ launches => (launch_top fixes.each_launch_reads_the_pool launches).1,
   fun _ _ _ _ launches in_pool not_given_up_on =>
      (launch_or_before fixes.each_launch_reads_the_pool launches in_pool not_given_up_on).imp id (outranks_iff ..).mp,
   fun _ _ _ launches => (launch_eq launches).1⟩

/-! ## The tools: what the Lua decides on their answers is what the model decides on its view -/

example (t : Tools) : AncestorReach t = ∀ w k b, t.isAncestor w k b = true → (t.git w).reachFrom k b = true := rfl
example (t : Tools) : SameContentReach t = ∀ w k b, t.sameContent w k b = true → (t.git w).reachFrom k b = true := rfl

/-- watchd.landed_ref saying "landed" means the commit is reachable from the branch, or `gh` said so.
Env: `AncestorReach`, `SameContentReach`. -/
theorem landed_ref_means_reachable_or_gh_said_so {t : Tools} (ancestor_reach : AncestorReach t)
    (same_content_reach : SameContentReach t) {w : t.World} {k b : Nat} {gh : Bool}
    (landed : landedRef t w k b gh = true) : (t.git w).reachFrom k b = true ∨ gh = true :=
  Tools.landedRef_reach ancestor_reach same_content_reach landed

example (t : Tools) : StatusClean t = ∀ w x, ((t.git w).wt x).on = true → t.statusClean w x = true →
    ((t.git w).wt x).dirty = false := rfl
example (t : Tools) : ListedOn t = ∀ w x, t.listed w x = true → ((t.git w).wt x).on = true := rfl
example (t : Tools) : CwdsProc t = ∀ w x, ((t.git w).wt x).proc = true → t.cwdIn w x = true := rfl
example (t : Tools) : TouchedRecent t = ∀ w x, ((t.git w).wt x).recent = true → t.now w < t.touched w x + sweepIdle := rfl

/-- The sweep's gate on the tools' answers (no `gh`) is W1's premise on the model's view.
Env: `AncestorReach`, `SameContentReach`, `StatusClean`, `ListedOn`, `CwdsProc`, `TouchedRecent`. -/
theorem sweep_gate_implies_w1_premise {t : Tools} (ancestor_reach : AncestorReach t)
    (same_content_reach : SameContentReach t) (status_clean : StatusClean t) (listed_on : ListedOn t)
    (cwds_proc : CwdsProc t) (touched_recent : TouchedRecent t) {w : t.World} {c : Cfg} {used : Bool} {x : Nat}
    (gate : sweepGate t w c used x (fun _ => false) = true) :
    let y := (t.git w).wt x
    y.on = true ∧ used = false ∧ y.proc = false ∧ y.recent = false ∧ y.dirty = false ∧ (t.git w).safe c y.head = true :=
  Tools.sweepGate_W1 ancestor_reach same_content_reach status_clean listed_on cwds_proc touched_recent gate

/-- What is assumed of hc here, as `Env.lean` defines it (tested by env_spec's `hc_ls_live`): `hc ls` lists a
terminal as live exactly when it is. Lean checks this line against the definition. -/
example (t : Tools) : HcLsLive t = ∀ w terminal, t.hcLs w terminal = t.termLive w terminal := rfl

/-- reap reads a bound row's terminal as gone (`hc ls` does not list it) exactly when it is gone. Env: `HcLsLive`. -/
theorem reap_reads_gone_iff_terminal_gone {t : Tools} (hc_ls_lists_the_live : HcLsLive t) {w : t.World}
    {terminal : Nat} : t.hcLs w terminal = false ↔ t.termLive w terminal = false :=
  Tools.reap_gone hc_ls_lists_the_live

example (db : Db) : SqliteBegin db = db.ByEngine (· = .begin) := rfl
example (db : Db) : SqliteRead db = db.ByEngine fun op => ∃ s, op = .stmt s ∧ Iso.sqlLang.writes s = false := rfl
example (db : Db) : SqliteWrite db = db.ByEngine fun op => ∃ s, op = .stmt s ∧ Iso.sqlLang.writes s = true := rfl
example (db : Db) : SqliteCommit db = db.ByEngine (· = .commit) := rfl
example (db : Db) : SqliteRollback db = db.ByEngine fun op => op = .rollback ∨ op = .close := rfl

/-- The db is serializable: every committed version is its transaction's statements run on the one before, and a
transaction holding the write lock runs on the latest. Env: all five sqlite assumptions. -/
theorem db_serializable {db : Db} (sqlite_begin : SqliteBegin db) (sqlite_read : SqliteRead db)
    (sqlite_write : SqliteWrite db) (sqlite_commit : SqliteCommit db) (sqlite_rollback : SqliteRollback db)
    {w0 w : db.World} {d0 : Sql.DB} (starts_at : db.view w0 = Iso.Eng.init d0) (runs : db.Run w0 w) :
    Iso.Inv Iso.sqlLang (db.view w) :=
  Db.serializable sqlite_begin sqlite_read sqlite_write sqlite_commit sqlite_rollback starts_at runs

end Swarm.Contract

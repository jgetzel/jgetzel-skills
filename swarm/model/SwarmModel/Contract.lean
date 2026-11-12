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
import SwarmModel.Checkers

/-! The contract (board #25): the theorems a proof about a program that uses the swarm should build on, each restated
here over the model's types (`Cfg`, `State`, `Reachable`, `Run`; `Env.Tools`, `Env.Db`), so a change to one that
breaks this statement breaks the build. Import this module alone (`example/Client.lean` does).

It is being rewritten to read top to bottom as the spec, to `../STYLE.md` (board #86): each statement after the
definitions it needs, as ∀, ∃ and named predicates; each proof a reference. S1, N1, L4, R1 (a') and "reap reads gone"
are done; the rest still have their older form.

Each says what it guarantees and what it rests on. "Switches" are the `Cfg` fields it takes as hypotheses: the fixes,
all on in `Cfg`'s defaults but `splitGC`, `perTaskBase`, `recordedWorkspaces`, `bgLives` and `ownAdded` (main has
them; `replay` sets them).
"Env" is which of `Env.lean`'s assumptions it takes, as hypotheses on any `Tools` or `Db`: the model theorems take
none. Nothing is assumed of a machine by axiom (board #68): a client supplies each hypothesis for its machine, by proof
(`Env.consistent` for `Env.ideal`) or as its own hypothesis, and `Trust.lean` shows each one taken here is needed. -/

namespace Swarm.Contract
open Env

/-! ## Safety: every reachable state, any number of agents, tasks, locks and messages -/

/-- Agent `a` is at work: working, or waiting at an hc prompt. -/
def AtWork (s : State) (a : Nat) : Prop := (s.agt a).st = .working ∨ (s.agt a).st = .blocked

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

/-- S1 at the board: a task an agent at work believes it holds is held by it on the board (claimed or blocked, it the
owner), or was dropped, or (board #80) watchd's poll marked it done when its PR merged (`merged`: the merge recorded),
which the agent hasn't read yet. Switches: `release = .idle`, `humanRelease` off. Env: none. -/
theorem s1_believes_held {c : Cfg} (hfix : c.release = .idle) (hhr : c.humanRelease = false) {s : State} (h : Reachable c s) {a t : Nat}
    (ha : active (s.agt a) = true) (ht : t ∈ (s.agt a).believes) :
    held (s.tk t) a = true ∨ (s.tk t).st = .dropped ∨ ((s.tk t).st = .done ∧ (s.tk t).merged = true) := by
  rcases (J_of_reachable hfix (Or.inl hhr) h).1 a t ht with hi | hd | hs
  · exact absurd hi.1 (by simp [ha])
  · exact hd
  · have := hs.1.1; rw [stopTo_none hhr h] at this; cases this

/-- S1 at the board, with H2 and its fix (board #53): a task an agent at work believes it holds is held by it, or was
dropped, or done by watchd's poll (board #80), or the user released it from that agent, which hasn't read the stop yet:
the task is open, its stop names the agent, and no one may take it (`stopped`). Switches: `release = .idle`,
`stopFirst`. Env: none. -/
theorem s1_believes_held_stop {c : Cfg} (hfix : c.release = .idle) (hsf : c.stopFirst = true) {s : State} (h : Reachable c s)
    {a t : Nat} (ha : active (s.agt a) = true) (ht : t ∈ (s.agt a).believes) :
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

/-- S2: no task was ever claimed while a task it is after wasn't done. Switches: `claimChecksDeps`. Env: none. -/
theorem s2_noEarlyStart {c : Cfg} (hfix : c.claimChecksDeps = true) {s : State} (h : Reachable c s) :
    noEarlyStart s = true :=
  noEarlyStart_of_reachable hfix h

/-- S3, as files: two live locks of different agents never both cover one path. Switches: `lockOverlap`, `lockForms`.
Env: none. -/
theorem s3_noSharedFile {c : Cfg} (hfix : c.lockOverlap = true) (hforms : c.lockForms = true) {s : State}
    (h : Reachable c s) {p q : Nat} {l m : Lock} {a b : Nat} (hp : s.lock[p]? = some l) (hq : s.lock[q]? = some m)
    (hpq : p ≠ q) (ha : l.holder = some a) (hb : m.holder = some b) (hab : a ≠ b) (he1 : l.exp = false)
    (he2 : m.exp = false) (x : String) (hx : Glob.Bytes x.toList) :
    ¬ (covers c x (c.pat p) = true ∧ covers c x (c.pat q) = true) :=
  noSharedFile_of_reachable hfix hforms h hp hq hpq ha hb hab he1 he2 x hx

/-- S4: no message is shown twice, and no cursor passes a message it didn't show. Switches: `deliverCas`. Env: none. -/
theorem s4_inboxExact {c : Cfg} (hfix : c.deliverCas = true) {s : State} (h : Reachable c s) : inboxExact s = true :=
  inboxExact_of_reachable hfix h

/-- S5: every done task has evidence. Switches: `evidenceRequired`. Env: none. -/
theorem s5_doneHasEvidence {c : Cfg} (hfix : c.evidenceRequired = true) {s : State} (h : Reachable c s) :
    doneHasEvidence s = true :=
  doneHasEvidence_of_reachable hfix h

/-- W1: a step removes a worktree only if it was clean, unattached, had no process inside and its HEAD on a protected
ref, and deletes a branch only if it is no protected ref and its tip was on one. Switches: `splitGC`. Env: none
(`env_sweepGate` is the same gate on the tools' answers). -/
theorem w1_gcOk (c : Cfg) (hc : c.splitGC = true) {s s' : State} (act : Action) (h : Reachable c s)
    (hs : step c s act = some s') : gcOk c s s'.git = true :=
  W1_of c hc s act s' h hs

/-- Worktree `w` has work that is not landed for agent `a`: it is there, and it is dirty or its HEAD is reachable from
no base of a task `a` owns (main, if it owns none). -/
def Unlanded (c : Cfg) (s : State) (a w : Nat) : Prop := s.git.landedIn (abases c s a) w = false

/-- Agent `a` holds work: its row is live, and a background job of its own runs, or the worktree it works in is
unlanded, or one it added is. -/
def HoldsWork (c : Cfg) (s : State) (a : Nat) : Prop :=
  (s.agt a).live = true ∧
    ((s.agt a).bg = true
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
  /-- workspace GC removes only what is clean and on a protected ref (W1, below) -/
  gc_removes_only_landed : W1 c

/-- `N1`, the form the counterexamples refute, says the same. -/
theorem noWorkLost_iff (c : Cfg) : N1 c ↔ NoWorkLost c :=
  ⟨fun h => ⟨fun s a r w => (keptBy_iff ..).mp (h.1 s a r ((holdsWork_iff ..).mpr w)), h.2.1, h.2.2.1, h.2.2.2⟩,
   fun h => ⟨fun s a r w => (keptBy_iff ..).mpr (h.1 s a r ((holdsWork_iff ..).mp w)), h.2, h.3, h.4⟩⟩

/-- The fixes N1 needs; each is needed (`not_N1_bgKeeps`, `not_N1_retake`, `not_N1_allWts`, `not_N1_bgLives`,
`not_N1_ownAdded` are runs that break it without). -/
structure N1Fixes (c : Cfg) : Prop where
  /-- reap reopens a lapsed claim only when its owner is idle -/
  reap_takes_from_idle_only : c.release = .idle
  /-- reap keeps a lapsed claim whose idle owner has a background job running (PR #121) -/
  reap_keeps_claim_while_job_runs : c.bgKeeps = true
  /-- the 350k fence on `task claim` lets a big agent take back what reap took from it (PR #121) -/
  fence_allows_claim_back : c.retake = true
  /-- lifecycle keeps an agent while any worktree it owns is unlanded, not only the one it works in (PR #123) -/
  lifecycle_checks_all_worktrees : c.allWts = true
  /-- lifecycle keeps an idle agent while its background job runs (board #15) -/
  lifecycle_keeps_agent_while_job_runs : c.bgLives = true
  /-- lifecycle also counts the worktrees a spawned agent added itself (board #15) -/
  lifecycle_counts_added_worktrees : c.ownAdded = true
  /-- "landed" means on a base of a task the agent owns, not on main alone (sw-bases, board #3) -/
  landed_is_per_task_base : c.perTaskBase = true
  /-- ending an agent removes no worktree: workspace GC alone does, by reachability from a protected ref (board #4) -/
  gc_alone_removes_worktrees : c.splitGC = true

/-- N1: watchd never discards work that isn't landed. Env: none. -/
theorem no_work_lost {c : Cfg} (fixes : N1Fixes c) : NoWorkLost c :=
  (noWorkLost_iff c).mp (N1_of c fixes.1 fixes.2 fixes.3 fixes.4 fixes.5 fixes.6 fixes.7 fixes.8)

/-- N1, W1 and W2 of a tick an error ends partway (`tickCut`, board #84; `Reachable.cut` makes every theorem above hold of
what it leaves). Switches: `N1`'s but `retake`. Env: none. -/
theorem n1_cut (c : Cfg) (hrel : c.release = .idle) (hbk : c.bgKeeps = true) (haw : c.allWts = true)
    (hbl : c.bgLives = true) (hoa : c.ownAdded = true) (hp : c.perTaskBase = true) (hs : c.splitGC = true) : N1cut c :=
  N1cut_of c hrel hbk haw hbl hoa hp hs

/-- a failed pass stops no other pass of the tick (board #84). Switches: `passGuard`. Env: none. -/
theorem passes_indep (c : Cfg) (hg : c.passGuard = true) : PassesIndep c := passesIndep_of hg

/-! ## Liveness: over fair runs (`Run.Fair`: every action enabled infinitely often in `fair` is taken) -/

/-- L2: a claimed task whose owner is idle is eventually done or open again, or its owner back at work, while no agent
starts a background job or dies. Switches: `racy = false`, `release ≠ .ended`, `watchd`. Env: none. -/
theorem l2_idleClaim {c : Cfg} (hr : c.racy = false) (hfix : c.release ≠ .ended) (hw : c.watchd = true) {a t : Nat}
    (ha : a ∈ c.agents) (ht : t ∈ c.tasks) (r : Run c) (hf : r.Fair) {n : Nat}
    (hq : ∀ k, n ≤ k → ∀ b, r.act k ≠ .bgStart b ∧ r.act k ≠ .die b)
    (hbg0 : ((r.st n).agt a).bg = false) (hdd0 : ((r.st n).agt a).dead = false)
    (h : idleClaim (r.st n) a t = true) : ∃ m, n ≤ m ∧ idleClaim (r.st m) a t = false :=
  idleClaim_leads_to hr hfix hw ha ht r hf hq hbg0 hdd0 h

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
`gone_terminal_row_is_ended` ends). Switches: none. Env: none. -/
theorem h2_released_reads {c : Cfg} (r : Run c) (hf : r.Fair) {n t : Nat} (hR : Reachable c (r.st n))
    (hact : r.act n = .releaseOther t) :
    ∃ o i, held ((r.st n).tk t) o = true ∧ ((r.st (n + 1)).msg i).kind = .released ∧ ((r.st (n + 1)).msg i).task = t ∧
      ∃ m, n + 1 ≤ m ∧ (active ((r.st m).agt o) = false ∨ ((r.st m).agt o).dead = true ∨ i ≤ (r.st m).cur o) :=
  released_reads r hf hR hact

/-- H1: `swarm end A` by the user or the communicator without --force never ends an agent that holds work (a background
job running, or work off its tasks' bases in a worktree it works in or owns): its check is lifecycle's but the 2 min.
`--force` does (`not_N1end_force`). Switches: `allWts`, `ownAdded`, `perTaskBase`. Env: none. -/
theorem h1_end_keeps_work {c : Cfg} (haw : c.allWts = true) (hoa : c.ownAdded = true) (hp : c.perTaskBase = true)
    {s s' : State} {a : Nat} (h : Reachable c s) (hs : step c s (.endOther a false) = some s') : holdsWork c s a = false :=
  N1end_of haw hoa hp s s' a h hs

/-- H1: `swarm end A` without --force changes nothing but A's row: A ended, no task, lock, message, cursor, git ref or
other agent changed. Switches: none. Env: none. -/
theorem h1_end_spec {c : Cfg} {s s' : State} {a : Nat} (hs : step c s (.endOther a false) = some s') :
    endable c s a = true ∧ s'.task = s.task ∧ s'.lock = s.lock ∧ s'.log = s.log ∧ s'.cursor = s.cursor ∧ s'.git = s.git ∧
      (a < s.ag.length → (s'.agt a).st = .ended) ∧ ∀ b, b ≠ a → s'.agt b = s.agt b :=
  endOther_spec hs

/-- Q1 (board #47): after a tick every blocked task's latest question was told. Switches: `renotify`. Env: none. -/
theorem q1_told {c : Cfg} (hr : c.renotify = true) : Q1 c := Q1_of hr
/-- A2 (board #47): a block notice is urgent exactly when the user is not away. Switches: `awayQuiet`. Env: none. -/
theorem a2_quiet {c : Cfg} (h : c.awayQuiet = true) : A2quiet c := A2quiet_of h
/-- A2 (board #47): on a run fair to the communicator's waiter, all it was sent before `--back` is read. Switches:
`backTells`. Env: none. -/
theorem a2_reaches {c : Cfg} (h : c.backTells = true) : A2live c := A2live_of h
/-- A3 (board #47): the away flag changes nothing the tick does but the notices' urgency. Switches: none. Env: none. -/
theorem a3_blind (c : Cfg) (s : State) (v : Option Nat) : blind (tickOf c (withAway s v)) = blind (tickOf c s) := A3 c s v

/-- N1' (board #50): `swarm nudge` changes no task, claim, lock, lease, message or cursor; it types its line into the
nudged agent's terminal only, starts or ends no terminal, and leaves the repo's durable state. Switches: none.
Env: `HcSendTargets`. -/
theorem n1'_nudge {t : Tools} (hs : HcSendTargets t) {c : Cfg} {s s' : State} {a : Nat}
    (h : step c s (.hnudge a) = some s') {w : t.World} {hT : Nat} (hl : t.termLive w hT = true) (l : String) :
    s' = s ∧ t.typed (t.hcSend w hT l) hT = t.typed w hT ++ [l] ∧
      (∀ h', h' ≠ hT → t.typed (t.hcSend w hT l) h' = t.typed w h') ∧
      (∀ h', t.termLive (t.hcSend w hT l) h' = t.termLive w h') ∧
      Git.durable (t.git (t.hcSend w hT l)) = Git.durable (t.git w) :=
  Tools.N1' hs h hl l

/-- Stays (board #79): the tick keeps a live stayer's row (but for the pool ids a digest told it of), and `swarm end`
without --force refuses it. Switches: none. Env: none. -/
theorem stay_kept {c : Cfg} {s : State} {a : Nat} (hs : (s.agt a).stay = true) (hl : (s.agt a).live = true) :
    { (tickOf c s).agt a with told := [] } = { s.agt a with told := [] } ∧ step c s (.endOther a false) = none :=
  ⟨tick_keeps_stayer hs hl, endOther_stay hs⟩
/-- Stays (board #48): `swarm stay --end A` by the user or the communicator changes A's stay alone (no task, claim,
lease, lock, message, cursor, git ref, event or other agent), and the tick after it keeps A while A holds work.
Switches: N1's. Env: none. -/
theorem st4_endStay {c : Cfg} (hrel : c.release = .idle) (hbk : c.bgKeeps = true) (hret : c.retake = true)
    (haw : c.allWts = true) (hbl : c.bgLives = true) (hoa : c.ownAdded = true) (hp : c.perTaskBase = true)
    (hsg : c.splitGC = true) {s s' : State} {a : Nat} (hr : Reachable c s) (h : step c s (.endStay a) = some s') :
    (s' = { s with ag := s'.ag } ∧ s'.ag.length = s.ag.length ∧
      ∀ b, s'.agt b = if b = a then { s.agt a with stay := false } else s.agt b) ∧
    (holdsWork c (reapLocks (reapTasks c s')) a = true → keptBy s' (tickOf c s') a = true) :=
  ⟨endStay_frame h, endStay_N1 (N1_of c hrel hbk hret haw hbl hoa hp hsg) hr h⟩
/-- Stays (board #79): `--back`'s digest lists a slot as hung exactly when its agent hung since away and did not end
since. Switches: none. Env: none. -/
theorem digest_hung' (c : Cfg) (s : State) (since a : Nat) :
    a ∈ (digestOf c s since).hung ↔
      a < c.nagents ∧ ∃ l1 l2, s.evs.drop since = l1 ++ .hung a :: l2 ∧ Ev.ended a ∉ l2 :=
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

/-! ## The tools: what the Lua decides on their answers is what the model decides on its view -/

/-- watchd.landed_ref saying "landed" means the commit is reachable from the branch, or `gh` said so.
Env: `AncestorReach`, `SameContentReach`. -/
theorem env_landedRef {t : Tools} (ha : AncestorReach t) (hsc : SameContentReach t) {w : t.World} {k b : Nat}
    {gh : Bool} (h : landedRef t w k b gh = true) : (t.git w).reachFrom k b = true ∨ gh = true :=
  Tools.landedRef_reach ha hsc h

/-- The sweep's gate on the tools' answers (no `gh`) is W1's premise on the model's view.
Env: `AncestorReach`, `SameContentReach`, `StatusClean`, `ListedOn`, `CwdsProc`, `TouchedRecent`. -/
theorem env_sweepGate {t : Tools} (ha : AncestorReach t) (hsc : SameContentReach t) (hsl : StatusClean t)
    (hlo : ListedOn t) (hcp : CwdsProc t) (htr : TouchedRecent t) {w : t.World} {c : Cfg} {used : Bool} {x : Nat}
    (h : sweepGate t w c used x (fun _ => false) = true) :
    let y := (t.git w).wt x
    y.on = true ∧ used = false ∧ y.proc = false ∧ y.recent = false ∧ y.dirty = false ∧ (t.git w).safe c y.head = true :=
  Tools.sweepGate_W1 ha hsc hsl hlo hcp htr h

/-- What is assumed of hc here, as `Env.lean` defines it (tested by env_spec's `hc_ls_live`): `hc ls` lists a
terminal as live exactly when it is. Lean checks this line against the definition. -/
example (t : Tools) : HcLsLive t = ∀ w terminal, t.hcLs w terminal = t.termLive w terminal := rfl

/-- reap reads a bound row's terminal as gone (`hc ls` does not list it) exactly when it is gone. Env: `HcLsLive`. -/
theorem reap_reads_gone_iff_terminal_gone {t : Tools} (hc_ls_lists_the_live : HcLsLive t) {w : t.World}
    {terminal : Nat} : t.hcLs w terminal = false ↔ t.termLive w terminal = false :=
  Tools.reap_gone hc_ls_lists_the_live

/-- The db is serializable: every committed version is its transaction's statements run on the one before, and a
transaction holding the write lock runs on the latest. Env: all five sqlite assumptions. -/
theorem db_serializable {db : Db} (hb : SqliteBegin db) (hr : SqliteRead db) (hw : SqliteWrite db)
    (hc : SqliteCommit db) (hrb : SqliteRollback db) {w0 w : db.World} {d0 : Sql.DB}
    (h0 : db.view w0 = Iso.Eng.init d0) (h : db.Run w0 w) : Iso.Inv Iso.sqlLang (db.view w) :=
  Db.serializable hb hr hw hc hrb h0 h

end Swarm.Contract

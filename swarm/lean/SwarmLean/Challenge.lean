import SwarmLean.ChallengeAnchor
import SwarmLean.Spec.Cross
import SwarmLean.Spec.Machine
import SwarmModel.Decide
import Std.Tactic.Do

/-!
# swarm-lean's main theorems, stated

This file is the one a person reads to know what swarm-lean's proofs guarantee (board #216). It states the main
theorems with `sorry` for their proofs; the proofs are where they always were, in `SwarmLean/Proofs/`, and
`SwarmLean/Solution.lean` gathers them. Nothing imports this file, and no `lake build` target builds it:
`challenge.sh` does, and runs the Lean FRO's Comparator (`lake comparator`, `comparator.json`) on the pair. Comparator
accepts only when

- every theorem below is proved in the solution with exactly the statement written here, using no axiom but
  `propext`, `Classical.choice` and `Quot.sound`, and the kernel accepts the proof;
- every definition a statement reads, down to Lean's core, is the same constant in both: so no proof can change what
  a statement means;
- every hole below has the same name and type in both.

## What is specification, and what is a hole

The statements read the world, the db and the code's data through definitions imported here in full, from modules
that import no proof and no implementation (`layering.sh` checks it):

- `Assumptions.lean`: the machine (`Tools`), a recorded run of the code on it (`Rec`, `RecM`, `Rec.go`), and every
  hypothesis a theorem takes about the world (`Atomic`, `GitReadsKeep`, `ToolsKeep`, `WtRemove`, …), each tested
  against the real tool by swarm-tests;
- `Db.lean`, `Db/Rows.lean`, `World.lean`, `Store.lean`, `Sys.lean`, `Util.lean`: the db's rows and the interfaces;
- `Spec/Data.lean`: the types the code's steps take and return, and the few functions of the code a hypothesis or an
  invariant reads (`Msgs.cursorOf`, `Locks.covers`, `Locks.overlaps`, `Run.runDirOk`, `Agents.HUMAN`,
  `Watchd.SWEEP_IDLE`);
- `Spec/Board.lean`, `Spec/Locks.lean`, `Spec/Msgs.lean`, `Spec/Cross.lean`, `Spec/Machine.lean`: the commands as
  data and each area's invariant (`Inv`, `Board.BInv`, `QueueProofs.QInv`, `Locks.Good`, `Inbox.MInv`,
  `Cross.XInv`), and the sweep's command lines.

The code's own functions are HOLES below: `def … := sorry` at their exact types, under their real names. The theorems
are about the solution's definitions of them, which are the functions the `swarm` binary runs (`Db/`, `Lib/`); that
the binary is built from them is trusted, not checked here. A hole is constrained only by what the theorems say of it.

After the holes come the definitions that name the code: each area's transactions as the CLI's own step functions
(`Board.TCmd.step`, `Inbox.MCmd.step`, …), the sweep's `Gate`, a run of sweeps and ends (`SweepProofs.Step.run`), and
the assumption `CwdsProc`, which reads `Machine.cwds`. They are a word-for-word copy of `Spec/Code.lean` and of
`Assumptions/Code.lean`'s `CwdsProc` (`challenge.sh` checks the text), and Comparator checks that each is the solution's
constant.

## Still trusted

Comparator and Lean's kernel (with `--paranoid`, five more checkers, each of which must accept too); bwrap, the sandbox `lake comparator` checks the solution's export in (the exports
themselves are made outside it, by the toolchain's `leanexport`, from this repo's own build: `challenge.sh`); the link
from the model to the real binary: the hypotheses of `Assumptions.lean` about the tools (tested, not proved), `RecM` as
the code's run on a machine, and `Real.lean`/`RealSys.lean`, the instances the binary runs the same code with; and the
machines `Proofs/Trust.lean` builds to show each of `sweepGate_W1`'s hypotheses is needed.
-/

/-! ## The holes: the code's functions the statements name -/

namespace SwarmLean
open Tasks Agents

/-- Hook context over 10,000 chars is replaced by a 2 KB preview the model never opens (msgs.CTX_CAP). -/
def Msgs.CTX_CAP : Nat :=
  sorry

/-- Posts a message from `frm` to `dest` (msgs.post): the db and the message's id. -/
def Msgs.post (db : Db) (now : Int) (frm dest body : String) (urgent : Bool := false)
  (kind : Option String := none) : Db × Nat :=
  sorry

/-- `name`'s unread messages by id: past its cursor, not its own, to it or to all (msgs.unread). -/
def Msgs.unread (db : Db) (name : String) : List Msg :=
  sorry

/-- `name`'s unread rows and the prefix `pick` chooses, that prefix marked read (msgs.take). One transaction, so no
other delivery moves the cursor in between. -/
def Msgs.take (name : String) (pick : List Msg → List Msg := id) (db : Db) : Db × List Msg × List Msg :=
  sorry

/-- deliver's step: the unread rows that fit in `budget` marked read, and how many stay unread. -/
def Msgs.deliverStep (name : String) (budget : Nat := Msgs.CTX_CAP) (db : Db) : Db × List Msg × Nat :=
  sorry

/-- watchd's delivery to the communicator once hc send typed its messages into its terminal (board #210): its unread
rows up to `i`, the last id typed, marked read; none when a `swarm read` since has passed them. -/
def Msgs.typedStep (name : String) (i : Nat) (db : Db) : Db × List Msg × List Msg :=
  sorry

/-- The waiter's decision on unread rows (msgs.wakes): the rows that wake it and whether one is urgent, or none.
Notices ride along and never wake; an urgent message always wakes, others unless `cold` (asked only then). -/
def Msgs.wakes.{u_1} {m : Type → Type u_1} [Monad m] (rows : List Msg) (cold : m Bool) :
  m (Option (List Msg × Bool)) :=
  sorry

/-- `n` has the communicator's rights: it, or the user (agents.in_charge). -/
def Agents.inCharge (db : Db) (envComms : Option String) (n : String) : Bool :=
  sorry

/-- Live agent rows, by name (agents.live_agents). -/
def Agents.live (db : Db) : List Agent :=
  sorry

/-- Live agents but the communicator, and the auto-spawn number and max (agents.limits). -/
def Agents.limits (db : Db) (envComms : Option String) : Nat × Option Int × Option Int :=
  sorry

/-- The fence on `name` from terminal `here` (HC_TERMINAL_ID), if any. -/
def Agents.fence (db : Db) (name : String) (here : Option String) : Option Fence :=
  sorry

/-- `name` is the user's, which no agent takes (agents.not_human). -/
def Agents.notHuman (name : String) : Except String Unit :=
  sorry

/-- Binds `name` to terminal `hc` (agents.bind's transaction), given the row as read before (`r`): refuses if it
changed since, logs a takeover from another terminal. -/
def Agents.bind (db : Db) (name : String) (cwd hc model : Option String) (r : Binding) (now : Int) :
  Db × Except String Unit :=
  sorry

/-- `swarm leave`: the row ends, what it held is released (agents.cmd_leave). -/
def Agents.leave (db : Db) (name : String) (now : Int) : Db :=
  sorry

/-- `swarm stay --end NAME` by `me` (in charge): clears a live agent's stay (agents.end_stay's transaction). -/
def Agents.endStay (db : Db) (me n : String) (now : Int) : Db × Except String Unit :=
  sorry

/-- `swarm away [note]` by `me`: sets the flag and tells the communicator `line`, unless already away (the flag
returned) (agents.cmd_away's transaction). -/
def Agents.goAway (db : Db) (me : String) (comms : Option String) (note line : String) (now : Int) :
  Db × Option (Option Int × Option String) :=
  sorry

/-- `swarm away --back` by `me`: clears the flag, keeps the digest and tells the communicator; none when the user was
not away (agents.cmd_away's back transaction). -/
def Agents.goBack (db : Db) (me : String) (comms : Option String) (now : Int) : Db × Option Digest :=
  sorry

/-- The ids a task waits on, in order (tasks.deps_of). -/
def Tasks.depsOf (r : Task) : List Int :=
  sorry

/-- SQL's `','||t.deps||',' like '%,'||d.id||',%'` for some not-done task `d`: `t` waits on an undone task. -/
def Tasks.blockedByDeps (db : Db) (t : Task) : Bool :=
  sorry

/-- The user released `r` from an agent still at work that has not read the stop (tasks.stop_pending). -/
def Tasks.stopPending (db : Db) (r : Task) : Bool :=
  sorry

/-- Lua's `title like 'main red: %'` as a sort key: 1 for a red task. -/
def Tasks.redKey (t : Task) : Nat :=
  sorry

/-- Order by `red desc, priority, id` (NULL priority first, as SQL sorts it). -/
def Tasks.boardLe (red : Task → Nat) (a b : Task) : Bool :=
  sorry

/-- Open tasks with no undone deps and no pending stop, red first then by priority (tasks.pool). -/
def Tasks.pool (db : Db) : List Task :=
  sorry

/-- `task add`: the new task's id. -/
def Tasks.add (c : Tasks.Ctx) (a : AddArgs) (db : Db) : Db × Except String Nat :=
  sorry

/-- `task claim`: `lease` is `--lease` as given. -/
def Tasks.claim (c : Tasks.Ctx) (id : Int) (lease : String) (db : Db) : Db × Except String Claimed :=
  sorry

/-- `task after`: what the deps became. -/
def Tasks.after (c : Tasks.Ctx) (id : Int) (deps : List Int) (db : Db) : Db × Except String Unit :=
  sorry

/-- `task priority`. -/
def Tasks.priority (c : Tasks.Ctx) (id p : Int) (db : Db) : Db × Except String Unit :=
  sorry

/-- `task renew`: the lease's new end. -/
def Tasks.renew (c : Tasks.Ctx) (id : Int) (lease : String) (db : Db) : Db × Except String Int :=
  sorry

/-- `n` may close landing task `r` (board #200): the lander `task land` named, an agent whose role has the word
lander, or the communicator (or the user). -/
def Tasks.isLander (db : Db) (comms : Option String) (n : String) (r : Task) : Bool :=
  sorry

/-- `task land` (board #200): the owner hands claimed task `id` at commit `sha` to a lander; it is landing, no
longer the owner's to hold, and not claimable until `task done` or `task unland`. -/
def Tasks.land (c : Tasks.Ctx) (id : Int) (sha : String) (lander : Option String) (db : Db) :
  Db × Except String Unit :=
  sorry

/-- `task unland` (board #200): the lander gives landing task `id` back as open, at P1 unless already lower, with the
reason appended to its body; its former owner, if live, and the communicator are told. -/
def Tasks.unland (c : Tasks.Ctx) (id : Int) (why : String) (db : Db) : Db × Except String Unlanded :=
  sorry

/-- `task done`. -/
def Tasks.done (c : Tasks.Ctx) (id : Int) (evidence : String) (db : Db) : Db × Except String DoneOut :=
  sorry

/-- `task block`: whether the user is away. -/
def Tasks.block (c : Tasks.Ctx) (id : Int) (question : String) (db : Db) : Db × Except String Bool :=
  sorry

/-- `task unblock`: the owner it is claimed by again. -/
def Tasks.unblock (c : Tasks.Ctx) (id : Int) (answer : String) (db : Db) : Db × Except String (Option String) :=
  sorry

/-- `task release`: who it was taken from (the communicator's release of another's task). -/
def Tasks.release (c : Tasks.Ctx) (id : Int) (after : Option (List Int)) (db : Db) :
  Db × Except String (Option String) :=
  sorry

/-- `task edit`: the fields changed and the task's state. -/
def Tasks.edit (c : Tasks.Ctx) (id : Int) (a : EditArgs) (db : Db) : Db × Except String (List String × Status) :=
  sorry

/-- `task drop`: the open tasks that wait on it; a done task is refused. -/
def Tasks.drop (c : Tasks.Ctx) (id : Int) (db : Db) : Db × Except String (List Task) :=
  sorry

/-- `swarm lock` on the repo-relative `path`: refused for an ended agent (a lock `swarm join` would bring back unchecked)
or when it overlaps a live peer's lock; else this agent's lock (insert or replace). An error leaves the db as it was
(the Lua's transaction rolls back). -/
def Locks.lock (c : Tasks.Ctx) (path reason lease : String) (db0 : Db) : Db × Except String Unit :=
  sorry

/-- `swarm unlock`: drops this agent's lock on `path`, if it has one. -/
def Locks.unlock (me path : String) (now : Int) (db : Db) : Db :=
  sorry

/-- Takes the tasks that left the board (done, dropped) out of the queue and closes the gaps. -/
def Queue.tidy (db : Db) : Db :=
  sorry

/-- `queue add`: puts `ids`, in their order, at `w`; an id already queued moves. -/
def Queue.add (c : Tasks.Ctx) (ids : List Int) (w : Queue.Place) (db : Db) : Db × Except String Unit :=
  sorry

/-- `queue rm`: takes `ids` out of the queue; an entry another agent queued only by the communicator or the user. -/
def Queue.rm (c : Tasks.Ctx) (ids : List Int) (db : Db) : Db × Except String Unit :=
  sorry

/-- `task hold`: the task is never staffed until `task unhold`. -/
def Queue.hold (c : Tasks.Ctx) (id : Int) (why : String) (db : Db) : Db × Except String Unit :=
  sorry

/-- `task unhold`. -/
def Queue.unhold (c : Tasks.Ctx) (id : Int) (db : Db) : Db × Except String Unit :=
  sorry

/-- The `swarm limits --queue-only` switch: unqueued tasks are backlog. -/
def Queue.queueOnly (db : Db) : Bool :=
  sorry

/-- Startable `main red:` tasks not held, in pool order. -/
def Queue.staffRed (db : Db) : List Task :=
  sorry

/-- Startable queued tasks not held (no red one), in queue order. -/
def Queue.staffQueue (db : Db) : List Task :=
  sorry

/-- The tasks to staff, in order: a red main's task, then the queue, then (queue-only off) the rest by priority; never
a held one. Auto-spawn staffs from it and an idle agent is told of it. -/
def Queue.staffing (db : Db) : List Task :=
  sorry

/-- Auto-spawn's next task: the first of `staffing` it has not given up on (`skip`). -/
def Queue.staffHead (skip : Task → Bool) (db : Db) : Option Int :=
  sorry

/-- `task done`, and the task leaves the queue; the count is of the tasks to staff after it. -/
def Queue.done (c : Tasks.Ctx) (id : Int) (evidence : String) (db : Db) : Db × Except String DoneOut :=
  sorry

/-- `task drop`, and the task leaves the queue. -/
def Queue.drop (c : Tasks.Ctx) (id : Int) (db : Db) : Db × Except String (List Task) :=
  sorry

/-- Reserves the agent and claims task `tid` for it, the task row as it was returned; `top` (auto-spawn): the claim
holds only while `tid` still heads the pool (tasks.reserve, inside cmd_spawn's transaction). -/
def Spawn.reserveTask (db : Db) (envComms : Option String) (name cwd : String) (tid : Int)
  (model : Option String) (now : Int) (top : Option (Db → Option Int) := none) : Db × Except Spawn.Refusal Task :=
  sorry

/-- The refs of bases (bases.refs). -/
def Bases.refs {m : Type → Type} [Monad m] [Git m] (names : List String) (cwd : Option String) : m (List String) :=
  sorry

/-- Each process's working directory, none when no process's can be read (callers then assume every dir is in use)
(machine.cwds). -/
def Machine.cwds {m : Type → Type} [Monad m] [Env m] [Fs m] [Proc m] [Sys m] : m (Option (List (Int × String))) :=
  sorry

/-- The protected bases (bases.protected): main, the default and every base a task names; `db` holds the tasks. -/
def Workspaces.protectedOf {m : Type → Type} [Monad m] [Fs m] [Git m] (db : Db) (cwd : Option String) :
  m (List String) :=
  sorry

/-- Nothing in worktree `wt` is unlanded relative to any of the refs `bs` (watchd.landed). -/
def Lifecycle.landed {m : Type → Type} [Monad m] [Proc m] [Sys m] (wt : String) (bs : List String)
  (main : Option String) : m Bool :=
  sorry

/-- Lifecycle's verdict on live agent row `a` (watchd.fate, model Decide.lean's fateL), and what it heard: none (kept:
staying, busy, idle under 2 min, in another swarm's or a busy terminal, holding a claim or lock, or, once its work is
landed, running a background job); "unclean", idle but kept by work not on its bases; "reuse", context under the
reuse threshold, an offer of related tasks (`Reuse.candidates`) not passed over, its waiter alive; else "end". `x`: its hc terminal; `hasTerms`: hc answered. With `all`
no check holds, so every one is made (the verdict is then meaningless). -/
def Lifecycle.fateHeard {m : Type → Type} [Monad m] (a : Agent) (t : Int) (x : Option Term) (hasTerms : Bool)
  (f : Lifecycle.Reads m) (all : Bool := false) : m (Option String × Lifecycle.Heard) :=
  sorry

/-- end_agent's transaction: if live row `n` is still idle on terminal `hc` with no stay, claim or lock (or `force`),
its holdings released and the row ended, with its event; true when it ended it. -/
def Lifecycle.endStep (n : String) (hc : Option String) (force : Bool) (by_ : Option String) (now : Int)
  (db : Db) : Db × Bool :=
  sorry

/-- Agent GC: re-checks that `a` is still idle on the same terminal with no claim, lock or stay (unless `force`),
releases and ends it (`endStep`), then kills its terminal and what it left in its cgroup scope; false when it changed
(watchd.end_agent). `by_`: who ended it by hand. -/
def Lifecycle.endAgent {m : Type → Type} [Monad m] [Fs m] [Proc m] [Store m] [Clock m] [Env m] (a : Agent)
  (force : Bool) (by_ : Option String) : m Bool :=
  sorry

/-- The owner row's columns `Decide.keepsL` reads: a NULL status is no status ("" is not "idle"). -/
def Watchd.keepRow (a : Agent) : Swarm.Decide.ARow :=
  sorry

/-- Whether owner row `o` keeps a claim past its lease for the work it is doing (watchd.keeps): the model's
`Decide.keepsL`, proved to be its `keeps` (`keeps_lifted`). Live, and working, prompt-blocked, running a background
job (`bg`) or in a compaction the swarm asked for (`compacting`), unless hc no longer lists its bound terminal (`live`:
the live addresses, none when hc can't tell). -/
def Watchd.keeps (o : Option Agent) (bg compacting : Bool) (live : Option (List String)) : Bool :=
  sorry

/-- Whether owner row `o` keeps a claim past its lease for being live (board #193), idle or not: not ended, bound to a
terminal hc still lists (or hc can't tell), and not flagged hung. An unbound row (a spawn that never launched) does not. -/
def Watchd.lives (o : Option Agent) (hung : Bool) (live : Option (List String)) : Bool :=
  sorry

/-- `p` is `wt` or under it (watchd.inside). -/
def Watchd.inside (p wt : String) : Bool :=
  sorry

/-- Reap's reopen of lapsed claim `r` (read before): only if the task is still claimed by the same owner with its lease
before `t` (a renew or re-claim since the read keeps it); the owner is told; true when it reopened it. -/
def Watchd.reapTask (r : Task) (t now : Int) (db : Db) : Db × Bool :=
  sorry

/-- Reap's drop of expired lock `l` (read before): only if that agent's lock on the path is still expired at `t` (a
fresh lock on the path since the read stays); true when it dropped it. -/
def Watchd.reapLock (l : Lock) (t now : Int) (db : Db) : Db × Bool :=
  sorry

/-- Reap of agent `n` whose terminal `h` hc no longer lists: only if the row is still live and bound to `h`; it ends,
what it held is released, everyone is told; true when it ended it. -/
def Watchd.reapGone (n h : String) (t : Int) (db : Db) : Db × Bool :=
  sorry

/-- The (path, branch) of each worktree `git worktree list --porcelain` lines list, the path as printed. -/
def Watchd.wtLines (ls : List String) : List (String × Option String) :=
  sorry

/-- Workspace GC: removes clean, landed worktrees (and their local branch) that no live agent or process uses; `dry`
only lists them. The worktrees and swept sizes (MB), and the "not landed" cache (worktree, HEAD and the bases' shas)
grown (watchd.sweep_worktrees, NOT_LANDED). With `dir` (a realpath), only the worktrees inside it are looked at. -/
def Watchd.sweep {m : Type → Type} [Monad m] [Store m] [Clock m] [Env m] [Fs m] [Proc m] [Git m] [Sys m]
  (comms : Option String) (dry : Bool) (notLanded : List String) (dir : Option String := none) :
  m (List (String × Option String × Int) × List String) :=
  sorry

/-- The branch of a worktree the sweep removed but stopped before deleting: each ended agent's branch gets
`branch -d`, which git refuses for one not merged into HEAD or checked out somewhere (a squash-landed one stays). -/
def Watchd.sweepBranches {m : Type → Type} [Monad m] [Proc m] (main : String) (ended prot : List String) :
  m Unit :=
  sorry

end SwarmLean

/-! ## The definitions that name the code: a copy of `Spec/Code.lean` -/

-- BEGIN CHALLENGE COPY
namespace SwarmLean
open Tasks

/-- A command's whole effect on the db, and its answer: the CLI's own step functions. -/
abbrev Cmd.step : Cmd → Db → Db × Result
  | .add c a, db => ((Tasks.add c a db).1, .added (Tasks.add c a db).2)
  | .claim c i l, db => ((Tasks.claim c i l db).1, .claimed (Tasks.claim c i l db).2)
  | .release c i af, db => ((Tasks.release c i af db).1, .released (Tasks.release c i af db).2)
  | .land c i s l, db => ((Tasks.land c i s l db).1, .landed (Tasks.land c i s l db).2)
  | .unland c i w, db => ((Tasks.unland c i w db).1, .unlanded (Tasks.unland c i w db).2)
  | .board, db => (db, .board db.tasks)

end SwarmLean

namespace SwarmLean.Board
open Tasks

/-- A command's effect on the db and whether it succeeded: the CLI's own step functions. -/
abbrev TCmd.step : TCmd → Db → Db × Bool
  | .add c a, db => ((Tasks.add c a db).1, (Tasks.add c a db).2.toBool)
  | .claim c i l, db => ((Tasks.claim c i l db).1, (Tasks.claim c i l db).2.toBool)
  | .after c i l, db => ((Tasks.after c i l db).1, (Tasks.after c i l db).2.toBool)
  | .priority c i p, db => ((Tasks.priority c i p db).1, (Tasks.priority c i p db).2.toBool)
  | .renew c i l, db => ((Tasks.renew c i l db).1, (Tasks.renew c i l db).2.toBool)
  | .done c i e, db => ((Tasks.done c i e db).1, (Tasks.done c i e db).2.toBool)
  | .block c i q, db => ((Tasks.block c i q db).1, (Tasks.block c i q db).2.toBool)
  | .unblock c i a, db => ((Tasks.unblock c i a db).1, (Tasks.unblock c i a db).2.toBool)
  | .release c i af, db => ((Tasks.release c i af db).1, (Tasks.release c i af db).2.toBool)
  | .edit c i a, db => ((Tasks.edit c i a db).1, (Tasks.edit c i a db).2.toBool)
  | .drop c i, db => ((Tasks.drop c i db).1, (Tasks.drop c i db).2.toBool)
  | .land c i s l, db => ((Tasks.land c i s l db).1, (Tasks.land c i s l db).2.toBool)
  | .unland c i w, db => ((Tasks.unland c i w db).1, (Tasks.unland c i w db).2.toBool)
  | .board, db => (db, true)

/-- The db after `cs` from `db`. -/
abbrev run (db : Db) (cs : List TCmd) : Db := (replay TCmd.step db cs).1

/-- Each command of `cs`, from `db`, with whether it succeeded. -/
abbrev trace (db : Db) (cs : List TCmd) : List (TCmd × Bool) := (replay TCmd.step db cs).2

end SwarmLean.Board

namespace SwarmLean.Locks
open Agents

/-- A command's whole effect on the db, and its answer: the CLI's own step functions. -/
abbrev LCmd.step : LCmd → Db → Db × LResult
  | .lock c p r l, db => ((Locks.lock c p r l db).1, .locked (Locks.lock c p r l db).2)
  | .unlock me p now, db => (Locks.unlock me p now db, .unlocked)
  | .leave n now, db => (Agents.leave db n now, .left)
  | .join n cwd hc model r now, db => match notHuman n with
    | .error e => (db, .joined (.error e))
    | .ok () => ((Agents.bind db n cwd hc model r now).1, .joined (Agents.bind db n cwd hc model r now).2)
  | .task c, db => ((c.step db).1, .task (c.step db).2)

end SwarmLean.Locks

namespace SwarmLean.Inbox
open Msgs

/-- A transaction's effect and the messages it showed: the CLI's own step functions. -/
abbrev MCmd.step : MCmd → Db → Db × List Msg
  | .post now f d b u k, db => ((Msgs.post db now f d b u k).1, [])
  | .read n, db => ((take n id db).1, (take n id db).2.2)
  | .deliver n b, db => ((deliverStep n b db).1, (deliverStep n b db).2.1)
  | .typed n i, db => ((typedStep n i db).1, (typedStep n i db).2.2)
  | .other f _, db => (f db, [])

/-- The db after `cs` from `db`. -/
abbrev run (db : Db) (cs : List MCmd) : Db := (replay MCmd.step db cs).1

/-- Each transaction of `cs`, from `db`, with what it showed. -/
abbrev trace (db : Db) (cs : List MCmd) : List (MCmd × List Msg) := (replay MCmd.step db cs).2

end SwarmLean.Inbox

namespace SwarmLean.Cross
open Board Agents

/-- Each transaction's effect on the db: the CLI's own steps, as each area's theorems run them. -/
abbrev XCmd.step : XCmd → Db → Db
  | .task c, db => (c.step db).1
  | .post now f d b u k, db => (Inbox.MCmd.step (.post now f d b u k) db).1
  | .read n, db => (Inbox.MCmd.step (.read n) db).1
  | .deliver n b, db => (Inbox.MCmd.step (.deliver n b) db).1
  | .typed n i, db => (Inbox.MCmd.step (.typed n i) db).1
  | .lock c, db => (c.step db).1
  | .end_ n hc force by_ now, db => (Lifecycle.endStep n hc force by_ now db).1
  | .reapTask r t now, db => (Watchd.reapTask r t now db).1
  | .reapLock l t now, db => (Watchd.reapLock l t now db).1
  | .reapGone n h t, db => (Watchd.reapGone n h t db).1

/-- The db after `cs` from `db`. -/
abbrev run (db : Db) (cs : List XCmd) : Db := cs.foldl (fun d x => x.step d) db

/-- The db after the first `k` transactions of the run `r` from `db`. -/
abbrev at_ (db : Db) (r : Nat → XCmd) : Nat → Db
  | 0 => db
  | k + 1 => (r k).step (at_ db r k)

end SwarmLean.Cross

namespace SwarmLean.SweepProofs

variable {M : Tools}

/-- What the sweep, run from state `s0`, checked of worktree `x` of the main checkout `m` before removing it, `L` the
calls it made before: `x` is listed (the realpath of a `worktree` line of the `git worktree list` it ran first, `m`
the first such line's), not the main checkout, used by no live agent of the db (realpaths read on one machine `w`), no process sat in it when
`Machine.cwds` read, untouched for `SWEEP_IDLE` and `status` clean (both read on one machine `wk`), and `landed` found
it landed on the refs of the protected bases. -/
structure Gate (s0 : Rec M) (m x : String) (L : List (M.World × Call)) : Prop where
  main : ∃ first, (lsLines s0.w).head? = some first ∧ m = realW (M.after s0.w lsArgv none) (first.drop 9).toString
  notMain : x ≠ m
  listed : ∃ e ∈ Watchd.wtLines (lsLines s0.w).tail, ∃ w : M.World, x = realW w e.1
  unused : ∃ w : M.World, ∀ p ∈ ((Agents.live s0.db).flatMap fun a => [a.wt.getD "", a.cwd.getD ""]).filter (· != ""),
    Watchd.inside (realW w p) x = false
  noProc : ∃ (s : Rec M) (cs : List (Int × String)), s.log <+: L ∧ (Rec.go (Machine.cwds : RecM M _) s).1 = .ok (some cs) ∧
    ∀ c ∈ cs, Watchd.inside (realW (Rec.go (Machine.cwds : RecM M _) s).2.w c.2) x = false
  idle : ∃ wk t, (wk, .git ["-C", x, "rev-parse", "--absolute-git-dir"] none) ∈ L ∧
    (wk, .cmd ["git", "--no-optional-locks", "-C", x, "status", "--porcelain"] none) ∈ L ∧
    (∃ st, (M.out wk ["git", "--no-optional-locks", "-C", x, "status", "--porcelain"] none).bind
      (fun o => if o.code == 0 then some o.stdout else none) = some st ∧ strip st = "") ∧
    (∃ st : Rec M, st.log <+: L ∧ t = M.now st.w) ∧
    Watchd.SWEEP_IDLE ≤ t - lastAt wk x (M.git wk ["-C", x, "rev-parse", "--absolute-git-dir"] none)
  landed : ∃ s sp sb : Rec M,
    (Rec.go (Lifecycle.landed x (Rec.val (Bases.refs (Rec.val (Workspaces.protectedOf s0.db (some m) : RecM M _) sp)
      (some m) : RecM M _) sb) (some m) : RecM M Bool) s).2.log <+: L ∧
    (Rec.go (Lifecycle.landed x (Rec.val (Bases.refs (Rec.val (Workspaces.protectedOf s0.db (some m) : RecM M _) sp)
      (some m) : RecM M _) sb) (some m) : RecM M Bool) s).1 = .ok true

/-- The worktree `x` of main checkout `m` passed `Gate` on the calls `L` before its removal, in the sweep that started
from some state. -/
abbrev GateAny (m x : String) (L : List (M.World × Call)) : Prop := ∃ sk : Rec M, Gate sk m x L

/-- What a step runs. -/
abbrev Step.run : Step → RecM M Unit
  | .sweep comms dry nl dir => discard (Watchd.sweep comms dry nl dir)
  | .branches main ended prot => Watchd.sweepBranches main ended prot
  | .stop a force by_ => discard (Lifecycle.endAgent a force by_)

end SwarmLean.SweepProofs
-- END CHALLENGE COPY

/-! ## The assumption that names the code: a copy of `Assumptions/Code.lean`'s `CwdsProc` -/

namespace SwarmLean

variable (M : Tools)

-- BEGIN CHALLENGE COPY Assumptions/Code.lean
/-- processes: `Machine.cwds`, when it answers, lists for every process inside a worktree a working directory whose
realpath (on the machine it left) is inside it (Linux: each /proc/<pid>/cwd; macOS: lsof) (env_spec: cwds_proc). -/
abbrev CwdsProc : Prop := ∀ (s : Rec M) cs wt, (Rec.go Machine.cwds s).1 = .ok (some cs) → M.Inside s.w wt →
  ∃ c ∈ cs, Watchd.inside ((M.realpath (Rec.go Machine.cwds s).2.w c.2).getD c.2) wt = true
-- END CHALLENGE COPY Assumptions/Code.lean

end SwarmLean

/-! ## Worktrees, branches and the end of an agent, on a machine (`Proofs/Sweep.lean`, `Proofs/Keep.lean`) -/

namespace SwarmLean.SweepProofs
attribute [local irreducible] String.startsWith String.drop SwarmLean.splitlines SwarmLean.strip String.splitOn String.intercalate SwarmLean.joinPath
open Std.Do
variable {M : Tools}

/-- **No work lost**, end to end: on a machine with these git, hc and cgroup assumptions, after any run of sweeps,
branch sweeps and ends from any state `s0`, every commit reachable before (from a branch, a tag, a remote ref or a worktree's HEAD) is reachable after, unless it
is the HEAD, or below the HEAD, of a worktree `x` that a `worktree remove` in the run took away, on the machine it ran
on, after `x` passed the sweep's `Gate` (which found it landed: `sweepGate_W1`); and every worktree there before is
there after, unless a `worktree remove` in the run took it away when it had nothing uncommitted, after it passed
`Gate`; and no worktree remove of the run took away a repo that is not one of `m`'s linked worktrees (another repo an
agent worked in, with no remote, say), nor one any live agent records as its `wt` or `cwd`: `Gate`'s `listed` and
`unused`. -/
theorem no_work_lost (hg : GitReadsKeep M) (ht : ToolsKeep M) (hwr : WtRemove M) (hbd : BranchD M) (hdr : DelRef M)
    (hrp : RevParseHead M) (hk : HcKillEnds M) (hr : HcRmKeeps M) (hc : CgroupKillKeeps M) (s0 : Rec M) (steps : List Step) :
    let s := (Rec.go (steps.forM (Step.run (M := M))) s0).2
    ((∀ c, M.Reach s0.w c → M.Reach s.w c ∨ ∃ i w m x k, s.log[i]? = some (w, .cmd (rmArgv m x) none) ∧
      GateAny m x (s.log.take i) ∧ M.head w x = some k ∧ M.Anc c k) ∧
    ∀ x, M.There s0.w x → M.There s.w x ∨ ∃ i w m, s.log[i]? = some (w, .cmd (rmArgv m x) none) ∧
      GateAny m x (s.log.take i) ∧ ¬ M.Dirty w x) ∧
    ∀ i w m x, s0.log.length ≤ i → s.log[i]? = some (w, .cmd (rmArgv m x) none) → ∃ sk : Rec M, x ≠ m ∧
      (∃ e ∈ Watchd.wtLines (lsLines sk.w).tail, ∃ w' : M.World, x = realW w' e.1) ∧
      ∃ w' : M.World, ∀ p ∈ ((Agents.live sk.db).flatMap fun a => [a.wt.getD "", a.cwd.getD ""]).filter (· != ""),
        Watchd.inside (realW w' p) x = false :=
  sorry

/-- W2 on a machine: ending an agent (its row, its terminal, its cgroup scope) changes no worktree, branch or commit. -/
theorem endAgent_keepsGit (ht : ToolsKeep M) (hk : HcKillEnds M) (hr : HcRmKeeps M) (hc : CgroupKillKeeps M) (w0 : M.World) (a : Agent)
    (force : Bool) (by_ : Option String) :
    ⦃fun s => ⌜M.SameRepo w0 s.w⌝⦄ (Lifecycle.endAgent a force by_ : RecM M Bool) ⦃⇓ _ s => ⌜M.SameRepo w0 s.w⌝⦄ :=
  sorry

/-- W1 on the code: every `git worktree remove` the sweep runs passed `Gate` on the calls before it. -/
theorem sweep_W1 (s0 : Rec M) (comms : Option String) (dry : Bool) (nl : List String)
    (dir : Option String) :
    ⦃fun s => ⌜s = s0⌝⦄ (Watchd.sweep comms dry nl dir : RecM M _) ⦃⇓ _ s => ⌜GoodFrom s0.log.length (Gate s0) s.log⌝⦄ :=
  sorry

/-- W1 on the machines the sweep's checks read, from `Gate`: the worktree it removes is the realpath of one that was
there when `worktree list` ran; no process was inside it when `Machine.cwds` read; it had nothing uncommitted when
`status` ran, if it was there; and it was not used in the `SWEEP_IDLE` before `status` ran, if git printed its git dir
then and the clock had not gone back since the sweep read it; and `landed` found its directory gone, or its HEAD
reached from one of the protected bases' refs (`Reached`). -/
theorem sweepGate_W1 (ha : AncestorReach M) (hsc : SameContentReach M) (hlo : ListedOn M) (hsl : StatusClean M)
    (hcp : CwdsProc M) (htr : TouchedRecent M) {s0 : Rec M} {m x : String} {L : List (M.World × Call)} (h : Gate s0 m x L) :
    (∃ (p : String) (w : M.World), M.There s0.w p ∧ x = realW w p) ∧
    (∃ s : Rec M, s.log <+: L ∧ ¬ M.Inside s.w x) ∧
    (∃ wk, (wk, .cmd ["git", "--no-optional-locks", "-C", x, "status", "--porcelain"] none) ∈ L ∧ (M.There wk x → ¬ M.Dirty wk x) ∧
      ∃ t, (∃ st : Rec M, st.log <+: L ∧ t = M.now st.w) ∧
        ∀ gd, M.git wk ["-C", x, "rev-parse", "--absolute-git-dir"] none = some gd → t ≤ M.now wk → ¬ M.Recent wk x) ∧
    ∃ s sp sb : Rec M, s.log <+: L ∧ (M.kind s.w x true = .none ∨ ∃ b ∈ Rec.val (Bases.refs (Rec.val
      (Workspaces.protectedOf s0.db (some m) : RecM M _) sp) (some m) : RecM M _) sb, Reached x "HEAD" b L) :=
  sorry

/-- `git -C main worktree remove wt` (the sweep's `rmArgv`) moves no branch tip, changes no other worktree, and changes
nothing when `wt` is dirty. -/
theorem wtRemove_only (hwr : WtRemove M) (w : M.World) (main wt : String) :
    let w' := M.after w (rmArgv main wt) none
    (∀ b, M.tip w' b = M.tip w b) ∧ (∀ x, x ≠ wt → (M.There w' x ↔ M.There w x) ∧ (M.Dirty w' x ↔ M.Dirty w x)) ∧
      (M.Dirty w wt → M.SameRepo w w') :=
  sorry

/-- deleteBranch's guarded path, `update-ref -d refs/heads/b k` (`BranchCall`, with `k` the HEAD the sweep read before
`landed`): if branch `b`'s tip changed, it was `k`; no other branch changed. -/
theorem delRef_guarded (hdr : DelRef M) (w : M.World) (main b k : String) :
    let w' := M.after w ["git", "-C", main, "update-ref", "-d", "refs/heads/" ++ b, k] none
    (M.tip w' b ≠ M.tip w b → M.tip w b = some k) ∧ ∀ b', b' ≠ b → M.tip w' b' = M.tip w b' :=
  sorry

end SwarmLean.SweepProofs

/-! ## Agents and watchd (`Proofs/Watchd.lean`) -/

namespace SwarmLean.WatchdProofs
open Agents Swarm

/-- St1 on the code: lifecycle neither ends nor reuses an agent that stays for something. -/
theorem fate_keeps_stayer {m : Type → Type} [Monad m] [LawfulMonad m] (a : Agent) (t : Int) (x : Option Term)
    (hasTerms : Bool) (f : Lifecycle.Reads m) (hs : (py a.stay).isSome = true) :
    Sat (fun r => r.1 ≠ some "end" ∧ r.1 ≠ some "reuse") (Lifecycle.fateHeard a t x hasTerms f) :=
  sorry

/-- What keeps a lapsed claim for its work, on the Lean row: a live owner, working, prompt-blocked, running a
background job or compacting, unless hc answered and no longer lists its bound terminal. -/
theorem keeps_iff (o : Option Agent) (bg cp : Bool) (live : Option (List String)) :
    Watchd.keeps o bg cp live = true ↔ ∃ a, o = some a ∧ a.ended = none ∧ (a.status ≠ some "idle" ∨ bg = true ∨ cp = true) ∧
      ¬ (live.isSome = true ∧ (py a.hc).isSome = true ∧ (live.getD []).contains (a.hc.getD "") = false) :=
  sorry

/-- Board #193: reap never reopens a claim whose live owner is in a compaction the swarm asked for (its turn ended and
it reads as idle), unless hc answered without its bound terminal. -/
theorem keeps_compacting {a : Agent} {bg : Bool} {live : Option (List String)} (he : a.ended = none)
    (hl : ∀ up, live = some up → (py a.hc).isSome = true → up.contains (a.hc.getD "") = true) :
    Watchd.keeps (some a) bg true live = true :=
  sorry

/-- Board #193: what keeps a lapsed claim for its owner being live: not ended, bound to a terminal, not hung, and hc
lists that terminal or can't tell. -/
theorem lives_iff (o : Option Agent) (hung : Bool) (live : Option (List String)) :
    Watchd.lives o hung live = true ↔ ∃ a, o = some a ∧ a.ended = none ∧ (py a.hc).isSome = true ∧ hung = false ∧
      ∀ up, live = some up → up.contains (a.hc.getD "") = true :=
  sorry

/-- `Decide.lives_lifted` is about the code that runs: watchd's `lives` is `Decide.livesL` on the owner row, so reap's
decision (`keeps o .. || lives o ..`) is `Decide.reap_lifted`'s. -/
theorem lives_eq (o : Option Agent) (hung : Bool) (live : Option (List String)) :
    Watchd.lives o hung live = Decide.livesL (o.map Watchd.keepRow) hung live :=
  sorry

/-- F1's `launch_top` on the code, with the queue (board #128): auto-spawn's reservation claims task `tid` only if,
in the transaction that claims it, `tid` heads the staffing order (`Queue.staffHead`, the tasks it has not given up on)
and the max held there (a free slot). So `tid` is startable and not held, and when no startable red task is left to
staff and some startable queued task is not held, `tid` is the first such in queue order. -/
theorem reserveTask_top {db : Db} {e : Option String} {name cwd : String} {tid : Int} {model : Option String}
    {now : Int} {skip : Task → Bool} {r : Task}
    (h : (Spawn.reserveTask db e name cwd tid model now (some (Queue.staffHead skip))).2 = .ok r) :
    Queue.staffHead skip db = some tid ∧ (∀ x, (limits db e).2.2 = some x → ((limits db e).1 : Int) < x) ∧
    (∃ t ∈ Tasks.pool db, (t.id : Int) = tid ∧ t.hold = none) ∧
    ∀ q, (∀ t ∈ Queue.staffRed db, skip t = true) → (Queue.staffQueue db).find? (!skip ·) = some q →
      tid = (q.id : Int) :=
  sorry

end SwarmLean.WatchdProofs

/-! ## Tasks and the board (`Proofs/Tasks.lean`) -/

namespace SwarmLean.Board
open Tasks

/-- The invariant holds after any task commands by any agents from the empty db. -/
theorem run_binv (cs : List TCmd) : BInv (run {} cs) :=
  sorry

/-- No task has two owners, after any task commands by any agents in any order from the empty db. -/
theorem one_owner_all (cs : List TCmd) (i : Int) (a b : String) (ha : Owns (run {} cs) i a)
    (hb : Owns (run {} cs) i b) : a = b :=
  sorry

/-- S5 (model: `done_task_has_evidence`): after any task commands from the empty db, every done task has evidence:
text that is not all whitespace. -/
theorem done_has_evidence (cs : List TCmd) : ∀ t ∈ (run {} cs).tasks, t.state = .done → EvOk t.evidence :=
  sorry

/-- S2 (model: `no_claim_before_dependencies_done`): a successful `task claim i` finds every task `i` is after done. -/
theorem claim_deps_done {c : Ctx} {i : Int} {l : String} {db : Db} {x : Claimed} {r : Task}
    (h : (Tasks.claim c i l db).2 = .ok x) (hr : db.find i = some r) :
    ∀ j ∈ depsOf r, ∀ u, db.find j = some u → u.state = .done :=
  sorry

/-- Under the store's assumption (`Atomic`), when processes ran any task commands at once with no successful release
of task `i` among them, at most one of them successfully claimed it. -/
theorem one_winner_all (before after : Db) (ran : List (TCmd × Bool)) (i : Int)
    (h : Atomic TCmd.step before after ran) (hr : ∀ x ∈ ran, ReleasedOf i x = false) :
    (ran.filter (ClaimedOf i)).length ≤ 1 :=
  sorry

/-- Of any task commands by any agents from any db, two successful claims of one task have a successful release of it
between them: a claim succeeds for at most one agent until the task is released. -/
theorem claimed_once_all (db : Db) (cs : List TCmd) (i : Int) (a b : TCmd × Bool) (ha : ClaimedOf i a = true)
    (hb : ClaimedOf i b = true) (t1 t2 t3 : List (TCmd × Bool)) (e : trace db cs = t1 ++ a :: t2 ++ b :: t3) :
    ∃ x ∈ t2, ReleasedOf i x :=
  sorry

/-- The pool is in board order (model: `ranked_sorted`). -/
theorem pool_sorted (db : Db) : (pool db).Pairwise (boardLe redKey · · = true) :=
  sorry

/-- The pool is exactly the open tasks that wait on no task not done and have no stop pending (model: `pool`,
`claimable`). -/
theorem mem_pool (db : Db) (t : Task) : t ∈ pool db ↔
    t ∈ db.tasks ∧ t.state = .open ∧ blockedByDeps db t = false ∧ stopPending db t = false :=
  sorry

/-- Stop first (model: `claimable`, `stopped`): `task claim` refuses a task released from an agent still at work that
has not read the stop. -/
theorem claim_not_stopped {c : Ctx} {i : Int} {l : String} {db : Db} {x : Claimed} {r : Task}
    (h : (Tasks.claim c i l db).2 = .ok x) (hr : db.find i = some r) : stopPending db r = false :=
  sorry

/-- A landing task is not claimable: `task claim` of it fails. -/
theorem claim_landing {c : Ctx} {i : Int} {l : String} {db : Db} {r : Task} (hr : db.find i = some r)
    (hs : r.state = .landing) (x : Claimed) : (Tasks.claim c i l db).2 ≠ .ok x :=
  sorry

/-- A landing task is closed only by its lander (the one named, an agent with role lander, or the communicator), and
only with evidence git found on the task's base. -/
theorem done_landing {c : Ctx} {i : Int} {e : String} {db : Db} {r : Task} {x : DoneOut} (hr : db.find i = some r)
    (hs : r.state = .landing) (h : (Tasks.done c i e db).2 = .ok x) :
    isLander db c.comms c.me r = true ∧ c.onBase = true ∧ x = .landed r.owner :=
  sorry

/-- A landing task's dependants keep waiting: a task that waits on it is not in the pool. -/
theorem landing_waits {db : Db} {x h : Task} (hx : x ∈ db.tasks) (hs : x.state = .landing) (hw : WaitsOn h x) :
    h ∉ pool db :=
  sorry

/-- `task land` hands over only its owner's claimed task, and leaves it landing with that owner. -/
theorem land_ok {c : Ctx} {i : Int} {s : String} {l : Option String} {db : Db} (h : (Tasks.land c i s l db).2 = .ok ()) :
    ∃ r, db.find i = some r ∧ r.state = .claimed ∧ r.owner = some c.me ∧
      ∃ r', (Tasks.land c i s l db).1.find i = some r' ∧ r'.state = .landing ∧ r'.owner = some c.me :=
  sorry

/-- F1 for a lander's close (board #200): a `task done` of landing task `x` puts in the pool an open task with no stop
pending that waits on no task not done but `x`. -/
theorem landed_frees {c : Ctx} {x : Int} {e : String} {db : Db} {o : Option String}
    (hi : Inv db) (hd : (Tasks.done c x e db).2 = .ok (.landed o)) {h : Task} (hm : h ∈ db.tasks)
    (ho : h.state = .open) (hs : stopPending db h = false)
    (hw : ∀ y ∈ db.tasks, y.state ≠ .done → WaitsOn h y → (y.id : Int) = x) : h ∈ pool (Tasks.done c x e db).1 :=
  sorry

/-- F1, `done_frees`: a `task done` of `x` puts in the pool an open task with no stop pending that waits on no task
not done but `x`. -/
theorem done_frees {c : Ctx} {x : Int} {e : String} {db : Db} {k : Int} {st : Option String} {n : Nat}
    (hi : Inv db) (hd : (Tasks.done c x e db).2 = .ok (.done k st n)) {h : Task} (hm : h ∈ db.tasks)
    (ho : h.state = .open) (hs : stopPending db h = false)
    (hw : ∀ y ∈ db.tasks, y.state ≠ .done → WaitsOn h y → (y.id : Int) = x) : h ∈ pool (Tasks.done c x e db).1 :=
  sorry

/-- F1, `release_waits`: a `task release` of `x` frees nothing: a task that waits on `x` is not in the pool after it. -/
theorem release_waits {c : Ctx} {x : Int} {af : Option (List Int)} {db : Db} {o : Option String}
    (hrel : (Tasks.release c x af db).2 = .ok o) {h : Task}
    (hw : ∃ ds, h.deps = some ds ∧ hasSub ("," ++ ds ++ ",") ("," ++ d x ++ ",") = true) :
    h ∉ pool (Tasks.release c x af db).1 :=
  sorry

end SwarmLean.Board

/-! ## Locks (`Proofs/Locks.lean`) -/

namespace SwarmLean.Locks
open Swarm
open Agents

/-- S3: after any lock, unlock, leave, join and task commands by any agents in any order from the empty db, at any time `t` no
earlier than each lock's clock, no two locks of different agents that hold at `t` (agent live, lease past `t`)
overlap. -/
theorem locks_disjoint (cs : List LCmd) (t : Int) (ht : Before t cs) : Disjoint (replay LCmd.step {} cs).1 t :=
  sorry

/-- S3 as files: no path is covered by two locks of different agents that hold at `t`. -/
theorem no_shared_file (cs : List LCmd) (t : Int) (ht : Before t cs) {l m : Lock}
    (hl : l ∈ (replay LCmd.step {} cs).1.locks) (hm : m ∈ (replay LCmd.step {} cs).1.locks)
    (h1 : HeldAt (replay LCmd.step {} cs).1 t l) (h2 : HeldAt (replay LCmd.step {} cs).1 t m) (hne : l.agent ≠ m.agent)
    (x : String) : ¬ (covers x l.path = true ∧ covers x m.path = true) :=
  sorry

/-- Under the store's assumption (`Atomic`), when processes ran lock, unlock, leave, join and task commands at once on a store
where S3 held at `t` (with every lock's agent live or the user), it still holds at `t`, if `t` is no earlier than
their locks' clocks. -/
theorem atomic_good (before after : Db) (ran : List (LCmd × LResult)) (t : Int) (h : Atomic LCmd.step before after ran)
    (ht : Before t (ran.map (·.1))) (hg : Good before t) : Good after t :=
  sorry

/-- `swarm lock` is granted exactly when the agent hasn't ended, the lease parses, and no lock of another agent that
holds at its clock (agent live, lease not expired) overlaps the path: an expired lock or a dead agent's never refuses. -/
theorem lock_ok_iff (c : Tasks.Ctx) (path reason lease : String) (db : Db) :
    (lock c path reason lease db).2 = .ok () ↔
      (∀ t w, fence db c.me c.here ≠ some (.ended t w)) ∧ (dur lease).isSome ∧
      ∀ m ∈ db.locks, HeldAt db c.now m → m.agent ≠ some c.me → overlaps path m.path = false :=
  sorry

/-- covers is its forms: the pattern as a literal path, its glob, and (no `*`, `?`, `[` in it) everything under it. -/
theorem covers_iff (path pat : String) :
    covers path pat = true ↔ ∃ f ∈ Glob.forms true (bytes pat), Glob.gm f (bytes path) = true :=
  sorry

/-- overlaps is exactly "some file both cover", a file name being bytes. -/
theorem overlaps_iff (p q : String) :
    overlaps p q = true ↔ ∃ w, Glob.Bytes w ∧ Glob.covers true w (bytes p) = true ∧ Glob.covers true w (bytes q) = true :=
  sorry

end SwarmLean.Locks

/-! ## Messages (`Proofs/Msgs.lean`) -/

namespace SwarmLean.Inbox
open Msgs

/-- S4. From a db that keeps the invariant, where agent `n` has its cursor (it joined), any transactions in any order
show `n`, over all their deliveries to it and in order, exactly the messages for it that its cursor moved past: each
once, in log order, and nothing else. -/
theorem exactly_once (db : Db) (cs : List MCmd) (n : String) (h : MInv db) (hn : (db.cursor n).isSome) :
    shownTo n (trace db cs) = window (run db cs) n (cursorOf db n) (cursorOf (run db cs) n) :=
  sorry

/-- S4 under the store's assumption (`Atomic`): when processes ran transactions at once on a store that keeps the
invariant, where `n` has its cursor, what their deliveries showed `n` is, up to order, exactly the messages for `n` its
cursor moved past. -/
theorem exactly_once_atomic (before after : Db) (ran : List (MCmd × List Msg)) (n : String)
    (h : Atomic MCmd.step before after ran) (hi : MInv before) (hn : (before.cursor n).isSome) :
    (shownTo n ran).Perm (window after n (cursorOf before n) (cursorOf after n)) :=
  sorry

/-- No message is shown twice: under `Atomic`, the deliveries to `n` show each message at most once. -/
theorem shown_once (before after : Db) (ran : List (MCmd × List Msg)) (n : String)
    (h : Atomic MCmd.step before after ran) (hi : MInv before) (hn : (before.cursor n).isSome) :
    (shownTo n ran).Nodup :=
  sorry

/-- Only the addressee is shown a message: under `Atomic`, every message shown to `n` is for `n`, and in the log. -/
theorem shown_for_it (before after : Db) (ran : List (MCmd × List Msg)) (n : String)
    (h : Atomic MCmd.step before after ran) (hi : MInv before) (hn : (before.cursor n).isSome) {r : Msg}
    (hr : r ∈ shownTo n ran) : ToIt n r ∧ r ∈ after.msgs :=
  sorry

/-- No cursor passes a message it didn't show: under `Atomic`, a message for `n` its cursor moved past was shown to
`n` by one of the deliveries. -/
theorem cursor_passes_only_shown (before after : Db) (ran : List (MCmd × List Msg)) (n : String)
    (h : Atomic MCmd.step before after ran) (hi : MInv before) (hn : (before.cursor n).isSome) {r : Msg}
    (hr : r ∈ after.msgs) (ht : ToIt n r) (h1 : cursorOf before n < r.id) (h2 : (r.id : Int) ≤ cursorOf after n) :
    r ∈ shownTo n ran :=
  sorry

/-- A post is unread by each agent it is for, right after it: the next delivery to that agent shows it (broadcast:
every agent but the sender, for `@all`). -/
theorem post_unread {db : Db} (h : MInv db) now frm dest body urgent kind {n : String} (hf : n ≠ frm)
    (hd : dest = n ∨ dest = "@all") :
    posted db now frm dest body urgent kind ∈ unread (Msgs.post db now frm dest body urgent kind).1 n :=
  sorry

/-- The waiter's decision on its unread messages (Decide.wakes_lifted): `swarm wait` wakes agent `n` exactly when a
message for `n` past its cursor wakes it, and one such is urgent or `n` is not cold. -/
theorem waiter_wakes (db : Db) (n : String) (cold : Bool) :
    (Id.run (wakes (unread db n) (pure cold))).isSome ↔
      (∃ r ∈ db.msgs, ToIt n r ∧ cursorOf db n < r.id ∧ Wakes r) ∧
      ((∃ r ∈ db.msgs, ToIt n r ∧ cursorOf db n < r.id ∧ Urgent r) ∨ cold = false) :=
  sorry

/-- A delivery to the ex-owner that shows it the stop lifts the stop (Release.deliver_released: the belief the stop
drops is the ex-owner's claim, which the task no longer holds; what the code keeps of it is `stopPending`). -/
theorem delivery_lifts_stop {db : Db} (h : MInv db) {o : String} {pick : List Msg → List Msg}
    (hpick : ∀ rows, pick rows <+: rows) {t : Task} (ho : py t.stop_to = some o) {r : Msg}
    (hr : r ∈ (take o pick db).2.2) (hs : t.stop_msg = some r.id) : Tasks.stopPending (take o pick db).1 t = false :=
  sorry

/-- The user's or the communicator's release of a task another holds (Release.releaseOther_unread): it posts the
ex-owner an urgent stop that the ex-owner has unread, and records that stop on the task. -/
theorem release_stop (c : Tasks.Ctx) (i : Int) (af : Option (List Int)) (db : Db) (h : MInv db) (f : String)
    (hr : (Tasks.release c i af db).2 = .ok (some f)) :
    ∃ r ∈ unread (Tasks.release c i af db).1 f, r.urgent = some 1 ∧
      ∃ t, (Tasks.release c i af db).1.find i = some t ∧ t.stop_to = some f ∧ t.stop_msg = some r.id :=
  sorry

/-- N1', the db half (Nudge.N1'_frame): `swarm nudge` writes only its event; the log is the only table it changes. -/
theorem nudge_frame (db : Db) (now : Int) (me ag : String) :
    { db.log now (some me) "nudge" (some ag) none with events := db.events, eventNext := db.eventNext } = db :=
  sorry

end SwarmLean.Inbox

/-! ## The queue and holds (`Proofs/Queue.lean`) -/

namespace SwarmLean.QueueProofs
open Tasks Queue

/-- Queue ops (`queue add`, `queue rm`, and `tidy`, which `task done`/`task drop` and watchd's done marks end with)
keep the places a permutation of 1..n. -/
theorem add_qinv (c : Ctx) (ids : List Int) (w : Place) (db : Db) (hi : Inv db) (hq : QInv db) :
    QInv (Queue.add c ids w db).1 :=
  sorry

theorem rm_qinv (c : Ctx) (ids : List Int) (db : Db) (hi : Inv db) (hq : QInv db) : QInv (Queue.rm c ids db).1 :=
  sorry

theorem done_qinv (c : Ctx) (i : Int) (e : String) (db : Db) (hi : Inv db) (hq : QInv db) :
    QInv (Queue.done c i e db).1 :=
  sorry

theorem drop_qinv (c : Ctx) (i : Int) (db : Db) (hi : Inv db) (hq : QInv db) : QInv (Queue.drop c i db).1 :=
  sorry

theorem tidy_qinv (db : Db) (hi : (db.tasks.map (·.id)).Nodup) : QInv (tidy db) :=
  sorry

/-- With an empty queue, queue-only off and no task held, the staffing order is exactly today's: the pool. -/
theorem staffing_today (db : Db) (hq : ∀ t ∈ db.tasks, t.qpos = none) (hh : ∀ t ∈ db.tasks, t.hold = none)
    (ho : queueOnly db = false) : staffing db = pool db :=
  sorry

/-- `task claim` refuses a held task, unless the communicator (or the user) gives --force. -/
theorem claim_not_held {c : Ctx} {i : Int} {l : String} {db : Db} {x : Claimed} {r : Task}
    (h : (Tasks.claim c i l db).2 = .ok x) (hr : db.find i = some r) :
    r.hold = none ∨ (c.force = true ∧ Agents.inCharge db c.comms c.me = true) :=
  sorry

/-- A held task is never staffed: not by auto-spawn, not told to an idle agent. -/
theorem staffing_not_held {db : Db} {t : Task} (h : t ∈ staffing db) : t.hold = none :=
  sorry

/-- With no startable red task left to staff, auto-spawn's next is the first startable queued task not held. -/
theorem staffHead_queue {db : Db} {skip : Task → Bool} {q : Task} (hr : ∀ t ∈ staffRed db, skip t = true)
    (hq : (staffQueue db).find? (!skip ·) = some q) : staffHead skip db = some (q.id : Int) :=
  sorry

/-- `task hold` and `task unhold` change the task's hold and nothing of the queue. -/
theorem hold_places (c : Ctx) (i : Int) (why : String) (db : Db) : places (Queue.hold c i why db).1 = places db :=
  sorry

theorem unhold_places (c : Ctx) (i : Int) (db : Db) : places (Queue.unhold c i db).1 = places db :=
  sorry

end SwarmLean.QueueProofs

/-! ## Across areas (`Proofs/Cross.lean`) -/

namespace SwarmLean.Cross
open Board Agents

/-- Cross-area safety: after any transactions of any areas, by any agents, in any order, from the empty db, every area's
invariant holds at any time `t` no earlier than each lock's clock: task ids unique, a claimed task has an owner and an
open one none, every done task has evidence (S5); the message log and cursors in order (S4's invariant); no two locks
of different agents that hold at `t` overlap (S3). -/
theorem run_xinv (cs : List XCmd) (t : Int) (ht : XBefore t cs) : XInv (run {} cs) t :=
  sorry

/-- No task has two owners, whatever every area did (`Board.one_owner_all` over all transactions). -/
theorem one_owner_x (cs : List XCmd) (t : Int) (ht : XBefore t cs) (i : Int) (a b : String)
    (ha : Owns (run {} cs) i a) (hb : Owns (run {} cs) i b) : a = b :=
  sorry

/-- S5 whatever every area did: every done task has evidence. -/
theorem done_has_evidence_x (cs : List XCmd) (t : Int) (ht : XBefore t cs) :
    ∀ u ∈ (run {} cs).tasks, u.state = .done → EvOk u.evidence :=
  sorry

/-- S3 whatever every area did: two locks of different agents that hold at `t` don't overlap. -/
theorem locks_disjoint_x (cs : List XCmd) (t : Int) (ht : XBefore t cs) : Locks.Disjoint (run {} cs) t :=
  sorry

/-- With processes at once: under `Atomic`, transactions of all areas that ran together from a db keeping every
invariant leave one that keeps them. -/
theorem atomic_xinv {before after : Db} {ran : List (XCmd × Unit)} {t : Int}
    (h : Atomic (fun x d => (XCmd.step x d, ())) before after ran) (ht : XBefore t (ran.map (·.1)))
    (hi : XInv before t) : XInv after t :=
  sorry

/-- L2 (model: `idleClaim_leads_to`), reap's half: on a run where reap, judging task `i` claimed by `o`, runs at some
point from `n` on with a clock past the lease `L`, the claim `(o, L)` does not last: at some point from `n` on the task
is no longer claimed by `o` with that lease (done, released, renewed, dropped, or reopened by that reap). -/
theorem claim_lapses (db : Db) (r : Nat → XCmd) (n : Nat) {i : Int} {o : String} {L : Int} {x : Task}
    (hx : (x.id : Int) = i) (ho : x.owner = some o)
    (hfair : ∃ m ≥ n, ∃ t now, r m = .reapTask x t now ∧ L < t) :
    ∃ m ≥ n, ¬ ClaimedBy (at_ db r m) i o L :=
  sorry

/-- L4 (model: `deadLive_leads_to`), reap's half: on a run where reap, finding terminal `h` gone from `hc ls`, runs on
row `a` at some point from `n` on, the row does not stay live and bound to `h`: at some point it is ended (its claims
and locks released, `WatchdProofs.reapGone_spec`) or bound elsewhere. -/
theorem gone_ends (db : Db) (r : Nat → XCmd) (n : Nat) {a h : String}
    (hfair : ∃ m ≥ n, ∃ t, r m = .reapGone a h t) : ∃ m ≥ n, ¬ BoundLive (at_ db r m) a h :=
  sorry

/-- St4 (model: `endStay_frame`, `Contract.end_stay_changes_only_the_stay`): `swarm stay --end A` by the user or the
communicator changes A's stay alone: every table but the agents and the event log as it was, every agent row as it was
but A's, and A's but for its stay, now none; or, refused, nothing. -/
theorem endStay_frame (db : Db) (me n : String) (now : Int) :
    let d := (endStay db me n now).1
    d.tasks = db.tasks ∧ d.locks = db.locks ∧ d.msgs = db.msgs ∧ d.cursors = db.cursors ∧ d.metas = db.metas ∧
      (d.agents = db.agents ∨ d.agents = db.agents.map fun a => if a.name = n then { a with stay := none } else a) :=
  sorry

/-- A1 (model: `away_keeps`): `swarm away` and `--back` change no task, lock, agent or cursor; the message log only
grows (the line to the communicator). -/
theorem away_keeps (db : Db) (me : String) (comms : Option String) (note line : String) (now : Int) :
    let d := (goAway db me comms note line now).1
    d.tasks = db.tasks ∧ d.locks = db.locks ∧ d.agents = db.agents ∧ Inbox.Grows db d :=
  sorry

theorem back_keeps (db : Db) (me : String) (comms : Option String) (now : Int) :
    let d := (goBack db me comms now).1
    d.tasks = db.tasks ∧ d.locks = db.locks ∧ d.agents = db.agents ∧ Inbox.Grows db d :=
  sorry

end SwarmLean.Cross

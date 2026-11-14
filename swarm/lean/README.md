# swarm-lean: the swarm CLI in Lean

The swarm CLI, ported from the Lua CLI it replaced (PORT.md: the decisions, the layout, how a command group is added;
board #110 deleted the Lua). It keeps the Lua CLI's command line and SQLite db. Lean 4.35.0, no Lean dependencies;
libsqlite3 from the repo flake.

## Install

The launcher `../swarm` runs `.lake/build/bin/swarm-lean` (or the nix link `.lake/nix`); when a source is newer than
the binary it still runs it, with one stderr line naming `./build.sh`, and with no binary it fails naming it (a hook
gets a "swarm hooks are OFF" note instead). That one command builds it either way:

- **elan + lake**: with `lake` on PATH ([elan](https://github.com/leanprover/elan) installs it and reads
  `lean-toolchain`), `lake build swarm-lean herdr-mods`, then a touch of the binary (lake keeps an up-to-date one's mtime).
- **nix**: otherwise, `nix build ../..#swarm-lean -o .lake/nix`, the repo flake's package (nixpkgs' Lean, which must
  match `lean-toolchain`). `nix run github:jgetzel/jgetzel-skills#swarm-lean -- board` also works, without the
  launcher's `SWARM_HERE`.

Rebuild after a pull that changes the sources. No prebuilt binaries are published: building from source is the only
route. The binary is about 11 MB: `c/shim.c` replaces `lean_initialize`, which Lean's `main` calls once any `Lean.*`
module is imported (here `Lean.Data.Json`) and which linked Lean's whole compiler library (120 MB before).

| File | What it is |
|---|---|
| `SwarmLean/Db.lean`, `Db/Rows.lean` | the db: every table as rows, the next ids |
| `SwarmLean/Db/*.lean` | each Lua module's pure steps, `… → Db → Db × Except String α` |
| `SwarmLean/Store.lean`, `World.lean`, `Sys.lean` | the interfaces (`Store`, `Clock`, `Env`, `Fs`, `Proc`, `Git`, `Sys`) |
| `SwarmLean/Real.lean`, `Sqlite.lean`, `c/shim.c` | the real world: the SQLite store, IO |
| `SwarmLean/Args.lean`, `Cmd/*.lean`, `Dispatch.lean`, `Main.lean` | argparse's grammar, the command groups, main |
| `SwarmLean/Herdr/*.lean` | the second executable, herdr-mods: the Herdr panels' installer and calendar feed (was Lua; `../../herdr-mods/herdr-mods` runs it through `../swarm` with `SWARM_EXE=herdr-mods`) |
| `SwarmLean/Assumptions.lean` | every assumption the proofs make about the world: `Atomic`, and the tools' (`Tools`) |
| `SwarmLean/Proofs.lean`, `Proofs/*.lean` | the theorems, about the functions the CLI runs (below) |
| `Audit.lean` | every theorem's axioms (Lean's three only, or it fails), and the theorems taking each assumption |
| `TestMain.lean`, `Tests/Cli/`, `Tests/Spec/` | `swarm-tests [pattern]`: the CLI's test suite (the Lua specs ported), parallel, per-test timeout |
| `Tests/*.lean` | the pure specs as `#guard`s, checked by `lake build` |
| `HarnessRetro/`, `HarnessRetroMain.lean` | `harness-retro <tool>`: the harness-retro skill's tools (transcript, time-report, harness-lint, probe-guard, probe-json), run by `../../harness-retro/<tool>.sh` |
| `test-harness-retro.sh` | those tools on `Tests/harness-retro`'s fixture, against what the Lua tools printed for it |
| `test-claim.sh` | 50 `task claim 1` processes on one db; exactly one wins |
| `hpl/` | the same sources built with hpl (`../../../high-perf-lean`), every module `--all` |
| `Report.lean` | `swarm-report`, swarm-retro's evidence report (its old swarm-report.lua), run by ../../swarm-retro/swarm-report |
| `build.sh` | builds the binary the launcher runs and swarm-report (elan's lake, else nix) |
| `check.sh` | build, no `sorry`/`axiom`, `Audit.lean`, each assumption's test tag, swarm-tests and test-claim.sh on both binaries |

## What is proved of the running code

Every theorem is about the functions the CLI runs: the pure steps it hands `Store.txn` (`Db/*.lean`, and the steps
named out of `Lib/Lifecycle.lean` and `Lib/Watchd.lean`), and the monadic decisions read through the world's classes.
No `sorry`, `admit`, `axiom` or `native_decide`; `Audit.lean` checks every theorem rests on Lean's three axioms only.
Concurrency is "any order of whole transactions": `Atomic`. A theorem that needs anything of the world takes it as a
hypothesis from `Assumptions.lean` (below).

**Tasks and the board** (`Proofs.lean`, `Proofs/Tasks.lean`). After any task commands, in any order, from the empty
db: task ids are unique and below the next id, a claimed task has an owner and an open one none, and every done task
has evidence that is not all whitespace (S5). No task has two owners. Two successful claims of a task have a
successful release between them; with processes at once (`Atomic`) and no release, at most one claim of a task
succeeds, exactly one when each would have won alone (what `test-claim.sh` runs). A successful claim found every task
it is after done (S2), the task open, no stop pending, the claimer under the context fence or retaking what reap took
from it. Each command's effect is stated (`after_spec` … `drop_spec`); the user's or the communicator's release of
another's task (H2) is always allowed on a claimed or blocked task, reopens it, records the stop and sends the ex-owner
one urgent message, and changes nothing else. The board's order is a total preorder and `task board` and the pool are
sorted by it; the pool is exactly the open tasks with no undone dependency and no stop pending; `task done` frees the
tasks waiting on it and `release --after` makes the task wait (F1's board half).

**Queue and holds** (`Proofs/Queue.lean`, board #128). `queue add`, `queue rm`, and the renumbering that `task done`,
`task drop` and watchd's done marks end with keep the queued tasks' places a permutation of 1..n (`QInv`) and change
nothing but the places and the events they log; `task hold`/`unhold` leave the places. The staffing order (auto-spawn,
an idle agent's digest) never holds a held task, its queue part is exactly the startable queued tasks not held, in queue
order; with an empty queue and queue-only off it is the pool without the held tasks, exactly the pool when none is held
(`staffing_today`). `task claim` of a held task succeeds only with the communicator's (or the user's) `--force`.

**Messages** (`Proofs/Msgs.lean`). Over any transactions, the deliveries to an agent show it, in order, exactly the
messages for it (from another sender, to it or to all) that its cursor moved past: each once, nothing else, and no
cursor passes a message it did not show (S4), with processes at once too. A post is unread by each addressee right
after it; an `@all` post is for everyone but the sender. The waiter wakes an agent exactly when an unread message for
it wakes and one is urgent or the agent is not cold, and an urgent one never asks whether it is cold. A release's stop
is unread by the ex-owner until a delivery shows it, which lifts it. A nudge writes only an event.

**Locks and the hook** (`Proofs/Locks.lean`). `covers` and `overlaps` are swarm/model's `Glob.lean`, built into the
binary: a pattern covers a path exactly when the path matches it as a glob or lies under it, and two patterns overlap
exactly when some path is covered by both. After any lock, unlock, leave, join and task commands, two locks of
different agents that hold at a time `t` share no file (S3), with processes at once too; `swarm lock` is granted
exactly when the agent has not ended, the lease parses and no live lock of another agent overlaps. The edit hook denies
exactly when another agent's live lock covers the path.

**Agents and watchd** (`Proofs/Watchd.lean`). watchd's `keeps` is the model's `Decide.keepsL` itself. For any answers
the world's reads give: lifecycle's verdict and every check it records are `Decide.fateRec`'s; it ends or reuses only
an agent idle 2 min with no stay, claim or lock, whose unlanded and job reads came back empty; a stayer is kept, and
`swarm end` refuses it; `swarm end` refuses exactly when `Decide.endWhyL` does. An end without `--force` that went
through found the agent live, idle on the terminal judged, staying for nothing and holding nothing, and it changes no
task and no lock. Reap reopens only a task still claimed by the owner it judged with a lapsed lease, drops only a lock
still expired, ends only a row still live and bound to the terminal hc no longer lists, and releases all it held.
Spawn's reservation finds fewer live agents than the max, auto-spawn's claim takes only the staffing order's top (a
startable task not held; the first startable queued one when no red main's task is left: `reserveTask_top`), and a failed
launch leaves no claim behind. A takeover refuses if the row changed since it was read. watchd's `guard` lets no
exception out of a pass.

**Across areas** (`Proofs/Cross.lean`, board #109). `XCmd` is every transaction above, of all four areas: the task
commands, post, read, deliver, lock, unlock, leave, join, `swarm end`/lifecycle's end and reap's three. After any of
them, by any agents, in any order, from the empty db, every area's invariant holds at once (`run_xinv`): ids, owners
and S5 (`done_has_evidence_x`), one owner per task (`one_owner_x`), S4's log in order, and S3 (`locks_disjoint_x`); with
processes at once under `Atomic` too (`atomic_xinv`). S4 holds with every transaction of every area interleaved
(`exactly_once_x`): those that are not deliveries only grow the log (`xcmd_grows`). On a run of transactions where reap
reaches a claimed task with a clock past its lease, the claim does not last (`claim_lapses`, L2's reap half); where
reap reaches a row whose terminal is gone, the row does not stay live and bound to it (`gone_ends`, L4's reap half).
`swarm stay --end A` changes A's stay alone (St4, `endStay_frame`); `swarm away` and `--back` change no task, lock,
agent or cursor (A1, `away_keeps`, `back_keeps`), and a second one is refused and changes nothing (A4).

**Workspace GC and the end, on a machine** (`Proofs/Sweep.lean`, `Proofs/Trust.lean`, board #115). `RecM` runs the code
on a machine (`Tools`) and records each command with the machine it ran on. Every `git worktree remove` the sweep runs
passed `Gate` on the calls before it (`sweep_W1`). On a machine with the git, cwd and mtime assumptions, a worktree that
passed `Gate` is listed and there, has no process inside, was clean when `status` read it, was not used in the last
30 min (when git printed its git dir and the clock did not go back), and its HEAD is reached from a protected ref unless
its directory is gone (`sweepGate_W1`); each of those six assumptions is needed (`need_sweep_*`). `worktree remove`
moves no branch and changes no other worktree (`wtRemove_only`), and the branch delete deletes only at the tip it read
(`delRef_guarded`). Ending an agent leaves every worktree, branch and commit as they were (`endAgent_keepsGit`, W2).

**The store** (`Proofs/Store.lean`, `Proofs/WriteBack.lean`, `Proofs/Migrate.lean`, board #134). The store's SQL is
data: `Db/Plan.lean`'s `Stmt`s, which Real.lean's `runStmts` runs (`storeDb` runs `dbPlan`, `connect` runs `migs`), and
`decodeRows`, which `loadRows` applies to what its select returned. Every row type's codec round-trips
(`decode_encode`), and decoding refuses rather than misreads: each cell of a decoded row is the value its field encodes
to, or one of the documented coercions (a number read as text, integral text or float read as an integer); anything
else is an error (`decode_reads`). Run by SQLite (`SqlExec`) on a table that holds exactly the rows loaded, the
write-back of a step's rows fails at no statement, leaves the table holding exactly those rows, keeps every column Lean
does not know of each row it keeps (a new row gets the defaults there), and changes no other table (`write_back`). A
table left as loaded gets no statement (`rowsPlan_same`); one that was not loaded gets an insert of each row the step
added (`rowsPlan_unloaded`). The plan skips the rows old and new share as a prefix, and on keyed rows equals the plan
over the whole lists (`rowsPlan_keyed`), so a step costs about the rows it changed (board #138). Loading a table returns its rows in key order whatever order SQLite gives them
(`load_rows`), so load after store is the identity on rows that are keyed, in key order and whose ints fit int64
(`store_load`). Each migration takes a db at schema version n (the first n of `migs` not needed) to version n+1, keeps
every cell the db had but a NULL task.deps the after migration fills, and run again changes nothing
(`migrate_version`); all of them take a db at any version to the last, where they change nothing (`migrateAll_last`).
Not covered: the next ids (`nextId` reads them, the store never writes them), and one theorem for all eleven tables at
once (each table's plan touches its table alone, so they compose).

**No work lost, end to end** (`Proofs/Keep.lean`, board #132). A run is any sequence of sweeps (watchd's, `--dry-run`'s)
and ends (`swarm end`, lifecycle's and hung's), from any state, on a machine with the git, hc and cgroup assumptions
`no_work_lost` takes (the table below). After it, every commit reachable before from a branch, a tag, a remote ref or a worktree's HEAD is
reachable after, unless it is the HEAD, or below the HEAD, of a worktree a `worktree remove` in the run took away, on
the machine it ran on, after that worktree passed the sweep's `Gate`; and every worktree there before is there after,
unless a `worktree remove` in the run took it away when it had nothing uncommitted, after it passed `Gate`
(`no_work_lost`). "Landed" is what `Gate` checked, as the code decides it (`Lifecycle.landed`, `sweepGate_W1`): the
worktree's directory was gone, or one of the protected bases' refs holds its HEAD by `merge-base --is-ancestor`, by
`diff --quiet` over the files it changed since the merge base (a squash or rebase merge), or by a merged PR whose head
is that commit (gh's word, assumed of nothing). The branch delete loses only what that same remove did: its guard is
the HEAD the sweep read before `landed` (`tie_lost`, `deleteBranch_kept`). The sweep alone: `sweep_kept`. Not in the run: spawn's undo of a failed launch
(`Workspaces.discardWs`, `worktree remove --force` and `branch -D` of the worktree it just made), and watchd's other
passes (their commands were read, not proved, to include no git write). Two fixes came with it: the sweep read HEAD
again after `landed`, so a commit made between the two reads was deleted with the branch, judged by the older HEAD;
and `Run.cleanRemote` took `.cache/swarm-run/../..` for a job's copy (`runDirOk` now refuses `..`).

**Crash safety** (`Proofs/Crash.lean`, board #133). `RecM` also records the db each transaction commits. Every
command group the CLI dispatches (`tasks_keeps` … `watchd_keeps`, all of them in `groups_keep`) and one watchd pass
(`pass_keeps`), run on any machine from a db where the cross-area invariant `XInv` holds, leave a db where it holds,
and so does the db after each transaction they commit on the way (`Keeps`). A process stopped at any point between
its steps (killed, or the machine gone) leaves the db it found or the one its last commit left (SQLite's atomic commit,
`AllOrNothing`), so the db it leaves keeps the invariant (`stopped_keeps`); a transaction in part is never seen. Each
theorem is proved by unfolding the command's own code down to its transactions and calls (`keeps_walk`) and closing each
transaction with a lemma for its step (`X.<step>`), from any db that keeps the invariant: with other processes' commits
in between too. A function with its own theorem under the name `K.<function>` (watchd's reap, lifecycle and pass) is
applied where it is called rather than walked again: one proof holding the whole pass needed more memory than CI has. A `repeat` loop is assumed to keep it (`LoopsKeep`, in the groups that have one: Msgs, Ci, Run, State,
Watchd and the pass); `loop_ends` proves that for every run of a loop that ends. Lean defines a loop only as a least
fixed point, and gives one that never ends an arbitrary value, so nothing can be proved of that run; its commits are
those of the turns before the stop, each of which keeps the invariant. Recovery: a dead agent's claim lapses and reap
reopens it (`claim_lapses`), its locks lapse and reap drops them (`lock_lapses`), and its row is ended once hc no longer
lists its terminal (`gone_ends`). A spawn that reserved an agent and died before the launch leaves an idle, unbound row
(`reserveAgent_row`) whose claim reap does not keep (`idle_unkept`), and lifecycle's verdict on it, idle 2 min and
holding nothing, is to end it (`unlaunched_ends`).

Each multi-step command, the gaps between its steps, and what covers a stop in each (between two transactions with
nothing else in between is always `*_keeps` with `stopped_keeps`):

| Command | Gap: stopped after | Covered by |
|---|---|---|
| any | a transaction | `*_keeps`, `pass_keeps`, `stopped_keeps`: the invariant holds |
| `spawn` | reserve (row live, idle, unbound; task claimed) | `reserveAgent_row`, `idle_unkept` + `claim_lapses`: the claim is reopened; `unlaunched_ends`: the row is ended |
| `spawn` | `git worktree add`, before its workspace row | not proved (liveness of the sweep): a fresh worktree at its base is clean and landed, so the sweep removes it once unused 30 min (`sweepGate_W1` proves only that it is safe to) |
| `spawn` | launch, before the `hc` address is recorded | not proved: the agent's first fenced write binds its row (`Agents.touch`) |
| `spawn` (failed launch) | `unreserve`, before `discardWs` | as the worktree gap above; `unreserve` itself drops the ended row's locks (finding F4, fixed) |
| `end`, lifecycle's end | the end's transaction, before `hc kill`/`hc rm`/the cgroup kill | F1, fixed: reap kills the terminal of an ended row that hc still lists and no live row is bound to (the cgroup's leftovers stay) |
| watchd sweep | `git worktree remove`, before the branch delete | F2, fixed: the branch sweep after each sweep runs `branch -d` on ended agents' branches (`sweepBranches_kept`, a step of `no_work_lost`'s run); a squash-landed one, which only `update-ref -d` deleted, stays |
| watchd sweep | inside `git worktree remove` | **finding F3**, open: a half-removed worktree is never pruned (`git worktree prune` would drop any vanished worktree's HEAD, breaking `no_work_lost`) |
| watchd reap | one reap transaction, before the next | the next pass judges again from the db: each reap step checks the row it acts on (`claim_lapses`, `lock_lapses`, `gone_ends`) |
| watchd `ci` check | the first transaction, before the git and gh reads | F5, fixed: a new red run's `ci-red` event and its task commit together after the reads (`ciCheckApply`); the first transaction (`ciCheckFirst`) leaves it alone |
| watchd conflict tick | a snapshot, before `tickApply` | the next tick redoes it: `tickApply` alone writes the pair keys |

F1: `Lifecycle.endAgent` commits the end, then runs `hc kill`, `hc rm` and the cgroup kill; killing first would kill an
agent that woke after the end's check, so reap kills an ended row's terminal instead. F2: the sweep removes the
worktree, then deletes its branch; stopped between, the next sweep no longer lists the worktree, so the branch sweep
(`Watchd.sweepBranches`) deletes ended agents' merged branches with `branch -d`, which git refuses for an unmerged or
checked-out one. F3: a `git worktree remove` killed midway leaves the admin entry with its directory partly or wholly
gone; the sweep skips a path that is not a directory. `git worktree prune` would also drop the admin entry, and so the
HEAD, of a worktree whose directory vanished with commits nothing else reaches, so it is left (nothing is lost, only
the entry stays). F5: `ciCheckStep` logs the `ci-red` event that keeps a second check from opening the task again; it
and the task now commit in one transaction, after the reads, and a check that finds another outcome by then commits
nothing. F4, `unreserve` keeping an ended row's locks, broke `XInv` and is fixed.

## What the proofs assume

All of it is in `SwarmLean/Assumptions.lean`, each a definition a theorem takes as a hypothesis (none is an axiom).
`Audit.lean` prints, for each, the theorems that take it.

| Assumption | About | Says | Taken by |
|---|---|---|---|
| `Atomic` | SQLite | processes' transactions that ran at once apply one after another in some order (stands for swarm/model's five sqlite hypotheses: the code's every write is one `BEGIN IMMEDIATE … COMMIT`; since #137 a read-only `Store.txn` is one WAL read transaction, and a write reuses what that read computed only when `pragma data_version` shows no commit since) | 13 theorems: `one_winner`, `exactly_one_winner`, `one_winner_all`, `atomic_good`, `exactly_once_atomic`, `atomic_inv`, `shown_once`, `shown_for_it`, `cursor_passes_only_shown`, `atomic_ran`, `end_atomic`, `reap_atomic`, `atomic_xinv` |
| `AllOrNothing` | SQLite | a process stopped mid-run leaves the db it found or as one of its transactions committed it, never a transaction in part | `stopped_keeps` |
| `SqlExec` | SQLite | each statement the store runs does what `Stmt.run` says: delete and update by key, insert with defaults that fails on a key a row has, `add column` with its default, the after migration | `write_back`, `store_load`, `runs_dels`, `runs_up`, `runs_ups`, `migrate_step`, `migrate_version`, `migrateAll_last` |
| `SqlSelect` | SQLite | `select cs from t` returns each row's cells, in some order | `load_rows`, `store_load` |
| `SqlTableInfo` | SQLite | `pragma table_info(t)` lists t's columns | `migrate_step`, `migrate_version`, `migrateAll_last`, `migrateAll_none` |
| `AncestorReach` | git | `merge-base --is-ancestor ref b` exiting 0 means `b` holds `ref`'s changes | `sweepGate_W1`, `gateW1`, `landedRef1_reach`, `landedRef1_reach_spec`, `landedRef_reach_spec`, `landed_reach_spec` |
| `SameContentReach` | git | `diff --quiet ref b -- <files ref changed since the merge base>` exiting 0 means the same | `sweepGate_W1`, `gateW1`, `landedRef1_reach`, `landedRef1_reach_spec`, `landedRef_reach_spec`, `landed_reach_spec` |
| `StatusClean` | git | an empty `status --porcelain` means nothing uncommitted | `sweepGate_W1`, `gateW1` |
| `ListedOn` | git | a worktree `worktree list` lists is there | `sweepGate_W1`, `gateW1` |
| `WtRemove` | git | `worktree remove` takes a clean worktree away and nothing else (what it leaves unreachable is below its HEAD), refuses a dirty one | `wtRemove_only`, `no_work_lost` |
| `DelRef` | git | `update-ref -d refs/heads/b k` deletes `b` only if its tip is `k`, nothing else; what it leaves unreachable is below `k` | `delRef_guarded`, `no_work_lost` |
| `BranchD` | git | `branch -d b` leaves every commit reachable (it deletes only a merged branch) and every worktree | `no_work_lost` |
| `RevParseHead` | git | `git -C x rev-parse HEAD`, when it prints a commit, prints `x`'s HEAD | `no_work_lost` |
| `GitReadsKeep` | git | the sweep's git reads (`GitRead`: worktree list, status, merge-base, diff, rev-parse) leave the repo as it was | `no_work_lost` |
| `ToolsKeep` | du, gh, lsof, hc | the sweep's other commands (`ToolRead`) leave the repo; a job's copy (`Run.runDirOk`) is not the repo | `no_work_lost` |
| `HcLsLive` | hc | `hc ls --json`, when it answers, lists a terminal live exactly when it is | none |
| `HcKillEnds` | hc | `hc kill h` ends `h` and leaves the repo | `endAgent_keepsGit`, `no_work_lost` |
| `HcRmKeeps` | hc | `hc rm h` leaves the repo | `endAgent_keepsGit`, `no_work_lost` |
| `HcSendTargets` | hc | `hc send h l` types `l` into `h` alone, starts or ends no terminal, leaves the repo | none |
| `HcRunStarts` | hc | `hc run --json --bg` that exits 0 started the terminal and pid it prints | none |
| `CgroupKillKeeps` | cgroups | "1" to a scope's `cgroup.kill` leaves the repo | `endAgent_keepsGit`, `no_work_lost` |
| `Kill0Alive` | OS | `kill(p, 0)` is 0 exactly when `p` is in the process table | none |
| `CwdsProc` | OS | `Machine.cwds` lists a directory inside every worktree a process sits in | `sweepGate_W1`, `gateW1` |
| `TouchedRecent` | filesystem | a worktree used in the last 30 min has an mtime within 30 min | `sweepGate_W1`, `gateW1` |
| `NowMono` | clock | `Clock.now` never goes back | none |
| `GhChecks` | gh | the verdict `Ci.verdict` reads off a listed PR is its checks' state | none |
| `GhState` | gh | a listed PR not closed is MERGED when merged, else OPEN | none |

`sql_consistent`: the model (`Stmt.run`) has the three SQLite assumptions. `consistent`: a machine on which no command runs has every tool assumption, so they are jointly satisfiable; that the
real tools have them is what the case in each tag tests (swarm-tests' env_spec and sqlite_spec, `Tests/Spec/Env.lean`
and `Sqlite.lean`, which check.sh requires to exist). Locks' `Before t cs` (S3's time `t` is no earlier than each lock's clock) is a condition of
the statement, not of the world: a clock that never goes back (`NowMono`) gives it at any moment after the locks.

## swarm/model's theorems: moved or not

Every theorem family of swarm/model (its README's properties and each file's theorems). **moved**: proved of the code
(the Lean theorem named), or the model file is the running code. **not applicable**: about the model's own machinery,
the Lua, or a model switch the code has built in; nothing of the code is lost with it. **not moved**: a property of the
swarm the code does not yet carry a proof of (why given). The deletion task (#110) may delete what is moved or not
applicable; what is not moved is the proof coverage lost with swarm/model. Four model files are not deletable at all:
`Glob.lean`, `Model.lean`, `PrWatch.lean` and `Decide.lean` are built into swarm-lean (lean_lib `SwarmModelGlob` in
lakefile.lean): `locks.covers`/`overlaps` and watchd's `keeps` are their functions. Move them under swarm/lean before
deleting swarm/model. #110 deleted only the model's link to the Lua (Lifted/, LockSrc, LoopSafe, the case generators,
case files and traces, SqlParse): every other model file has a not-moved theorem or is imported by one that has
(swarm/model/README.md, first section).

| Model family (file: theorems) | Status | Lean theorem / why |
|---|---|---|
| Model: `reachable_of_run`; Frame: all; Basic: `evL_*`, `reachable_induct`, `when_eq_some` | not applicable | the model's state, `step` and induction; the code's steps are their own definitions |
| Basic: `noEarlyStart_of_reachable` (S2) | moved | `Board.claim_deps_done` (a latch on claims: per step is all of it) |
| Basic: `doneHasEvidence_of_reachable` (S5) | moved | `Board.done_has_evidence`; with every area: `Cross.done_has_evidence_x` |
| Workers: `oneWorker_of_reachable` (S1), `J_*`, `HS_*`, `pfx_*`, `own_unique`, `held_*`, `rel_*` | not moved | S1 is about agents' beliefs (what their commands told them) and being at work: the db has no such state. Its board half is moved: `Board.one_owner_all`, `Cross.one_owner_x`, `claimed_once_all`, `one_winner_all`, `claim_not_stopped`, `Inbox.delivery_lifts_stop` |
| Glob: `covers_iff`, `overlaps_iff`, `overlaps_complete`, `overlaps_comm`, `covers_eq`, `covers_not_subsume*`, its lemmas | moved | the running code (built into the binary); restated as `Locks.covers_iff`, `overlaps_iff`, `overlaps_of_covers`, `overlaps_comm` |
| Locks: `locksDisjoint_of_reachable` (S3), `noSharedFile_of_reachable`, `lkInv_of_reachable`, `lk_*` | moved | `Locks.locks_disjoint`, `no_shared_file`, `atomic_good`, `Good`; with every area (reap's lock drop and end included, the model's `lk_tickOf`, `lk_tickCut`, `lk_endAgent`): `Cross.run_xinv`, `locks_disjoint_x` |
| Locks: `liveL_*`, `shrinks_*`, `getD_modify`, `setAg_ag`, `refuses_eq`, `overlap_comm` | not applicable | list-index lemmas of the model's state |
| Inbox: `inboxExact_of_reachable` (S4), `inbInv_of_reachable`, `ii_*`, `mem_unread`, `unread_pairwise` | moved | `Inbox.exactly_once`, `exactly_once_atomic`, `shown_once`, `cursor_passes_only_shown`, `MInv`, `run_inv`; the tick's parts (`ii_endAgent`, `ii_reapTask`, `ii_tickOf`, `tick_inv*`, `tickCut_inv*`): `Cross.xcmd_grows`, `exactly_once_x` |
| Inbox: `ii_wakeRead`, `ii_reset`, `showMsg_*`, `showAll_*`, `msg_*`, `addressed_*`, `getD_set`, `agt_*`, `tk_*`, `sp_*`, `spawn_fold`, `ii_spawnFor`, `ii_pollOf`, `claimed_stop` | not applicable | the racy split read/write (the code's delivery is one transaction), ghosts and indexing lemmas; spawn's and the poll's writes are monadic loops whose db steps post through `Msgs.post` (`grows_post`) |
| Decide: `keeps_lifted`, `keeps_gap`, `fate_*`, `fateRec_*`, `report_lifted`, `orRec_vals`, `endWhy_*`, `wakes_lifted`, `wakesL_all`, `prAct_lifted` | moved | the running code (built into the binary); `WatchdProofs.keeps_eq`/`keeps_iff`, `fateHeard_rec`, `fate_lifted`, `fate_end_free`, `fateHeard_all`, `endWhy_lifted`, `prAct_eq`; `Inbox.waiter_wakes`, `wakes_spec`, `wakes_urgent` |
| DecideCases, GlobCases, LuaCases, SqlCases, Traces; LockSrc, Lifted/*, LoopSafe's `Ok`/`Owns` rules | not applicable | generators of the Lua specs' cases, the Lua as syntax and its lifts: about the Lua, deleted with it |
| Liveness: `tick_reopens`, `reapTask_fires`, `idleClaim_not_stuck`, `deadLive_not_stuck` | moved | `Cross.claim_lapses`, `Cross.gone_ends` (reap fires on a claimed task past its lease, on a row bound to a gone terminal) |
| Fair: `idleClaim_leads_to` (L2), `expire_lapses`, `Run.fair_ev`, `forever`; its `Th_*`, `persist` lemmas | moved (reap's half) | `Cross.claim_lapses`: on a run where reap reaches the task with a clock past the lease, the claim ends. Not moved: that watchd's monadic `reap` pass issues that transaction for an idle owner it doesn't keep, and that time passes; here both are the run's hypothesis |
| Gone: `deadLive_leads_to` (L4), `rz_*` | moved (reap's half) | `Cross.gone_ends` (and `reapGone_spec`: then the row holds nothing). Not moved: that the pass issues it when `hc ls` omits the terminal (`HcLsLive`, the monadic `reap`). `rz_*`: the racy read, not applicable |
| Taken: `startable_taken` (L1), `claimable_taken`, `ready_step`, `tick_ready`, `lifecycle_fills`, `stopped_step`, `stop_kept`, `grow_step`, `SK` | not moved | L1 needs the agents' behaviour (an agent with a small context and no claim takes work) and auto-spawn's monadic loop: neither is code with a proof. The steps are moved: `Board.claim_enabled`, `mem_pool`, `WatchdProofs.reserveTask_top` |
| Taken: `claim_enabled`, `startable_of_claimable` | moved | `Board.claim_enabled`, `Board.mem_pool` |
| Holder: `holder_leads_to`, `pa_step`, `unblock_pa`, `gk_*`, `bf_*`, `Tp_*`; Boot: `booting_reads`, `boot_reads`, `Q_*`; Answer: `answer_reaches` (L3), `l3_*`, `owner_*` | not moved | L3 is the holder reading its inbox at its turns, and a spawned holder booting before its lease lapses: agents' behaviour, not code. The code's part is moved: `Board.unblock_spec` (the answer on the task, the owner kept), `Inbox.post_unread` and `exactly_once` (the answer's message reaches the holder once) |
| Answer: `unblock_owner`, `drop_frees`, `releaseOther_frees` | moved | `Board.unblock_spec`, `drop_spec`, `release_other_spec` |
| Release: `releaseOther_enabled`, `releaseOther_spec` (H2) | moved | `Board.release_other_enabled`, `release_other_spec` |
| Release: `deliver_released`, `showMsg_released`, `showAll_believes_sub`, `releaseOther_unread` | moved | `Inbox.delivery_lifts_stop`, `release_stop` |
| Release: `stop_read`, `released_reads`, `stop_lifts`, `startable_leads_to` | not moved | liveness of the ex-owner reading the stop at its turns: agents' behaviour |
| Release: `stopTo_none`, `not_S1_humanRelease` | not applicable | runs with a model switch off; the code has stop-first (`claim_not_stopped`) |
| End: `endOther_spec`, `N1end_of` (H1), `endOther_enabled`, `finished_eq`, `releaseAll_free` | moved | `WatchdProofs.endStep_free`, `endStep_frame`, `endStep_ends`, `end_atomic`, `endWhy_lifted`, `release_free` |
| End: `endOther_git` | moved | `SweepProofs.endAgent_keepsGit`: `Lifecycle.endAgent` (its row, `hc kill`, `hc rm`, the cgroup kill) leaves every worktree, branch and commit, on a machine with `HcKillEnds`, `HcRmKeeps`, `CgroupKillKeeps` |
| End: `endOther_force`, `not_N1end_force*` | not applicable | `--force` skips the check by design |
| NoWorkLost: `N1_of`, `replay_N1`, `finished_of_holds`, `lifecycle_keeps`, `reapTask_keeps`, `lifecycle_tk` | moved | (1) as the model now states it: a stalled job (a sleep loop or a hung tree, `idleJob`) is not work (#106's finding, board #125: the model's `bgStall`; `hungStep_hung` on the code; `idleJob`'s loop itself is not proved). Moved: `fate_end_free`, `endStep_free`, `keeps_bg`, `keeps_iff`, `reapTask_spec`, `reap_atomic`. (4), W1's part: `SweepProofs.sweep_W1`, `sweepGate_W1` |
| NoWorkLost: `not_N1_*`, `pre*`, `cfg*` | not applicable | runs with a fix switched off |
| Spawn: `Sp1_of`, `Sp2_of` | moved | `WatchdProofs.unreserve_spec`, `reserve_max` |
| Spawn: `Sp3_of`, `noSpawn_startable`, `first_pool`, `tickG_id`, `sfail_eq`, `failed_s`, `tk_endAgent_keep`, `lifecycleG_nil_keep` | not moved | Sp3 is auto-spawn's backoff over fair runs, decided in the monadic `autoSpawn` loop; the rest are its model world's lemmas |
| Staff: `done_frees`, `release_waits`, `launch_top`, `launch_or_before`, `before_total`, `nbefore_trans`, `ins_sorted`, `ranked_sorted` (F1) | moved | `Board.done_frees`, `release_waits`, `boardLe_total`, `boardLe_trans`, `board_sorted`, `pool_sorted`, `WatchdProofs.reserveTask_top` |
| Staff: `mem_ins`, `mem_ranked`, `before_spec`, `find_top`, `launch_eq`, `stopped_unbelieve`, `not_F1` | not applicable | the model's insertion sort, order and beliefs; a run with `freshPool` off |
| Stay: `stayer_kept`, `tick_keeps_stayer`, `endOther_stay` (St1) | moved | `WatchdProofs.fate_keeps_stayer`, `endWhy_stayer` |
| Stay: `endStay_frame`, `endStay_spec`, `endStay_enabled`, `endStay_N1`, `holdsWork_stay` (St4) | moved | `Cross.endStay_frame`, `endStay_enabled` (the stay is no part of what fate or end_why counts as work: `fate_end_free` reads it only to keep) |
| Stay: `stay_spec`, `stayCheck_spec`, `stayHung_spec`, `digest_hung` (St2, St3) | not moved | `stay` runs inside `fenced` (touch) and was not stated; the check and the hang are `Watchd.hung`, a monadic loop over events; the digest is `Agents.digest` (not stated) |
| Away: `away_keeps`, `away_twice`, `back_twice` (A1, A4) | moved | `Cross.away_keeps`, `back_keeps`, `away_twice`, `back_twice` |
| Away: `Q1_of`, `tick_keeps_blocked`, `holds_of_blocked`, `back_questions`, `A2quiet_of`, `A2live_of`, `A3`, `since_kept`, `back_digest`, `questions_sorted`, `digest_*`, `notify_*`, `notices_*`, `side_step`, `cbox_grows`, `toldAfter_*` | not moved | the block notices are `Watchd.quiet`/`blockers`, monadic loops; the digest is `Agents.digest`, not stated; A2's liveness is the communicator's reads |
| Away: `not_Q1*`, `not_A2*`, `lassoBT`, `blind_*`, `foldl_wa`, `tickS_wa`, `st_take` | not applicable | refutations with a switch off, and the model's frames |
| Nudge: `N1'_frame` | moved | `Inbox.nudge_frame` |
| Nudge: `Tools.N1'`, `hnudge_enabled`, `hnudge_reachable` | not moved | the nudge's `hc send` and its refusals are in the monadic `Cmd.Msgs.nudge`; `HcSendTargets` is stated (Assumptions.lean) but no theorem takes it yet |
| PrWatch: `P1_of`, `P2_of`, `main_P1`, `main_P2`, `poll_*`, `merged*`; Merged: `poll_ends`, `P1_of`, `P2_of`, `main_P*`, `owner_live`, `pollOf_ne` | not moved | the poll's decision is moved (`WatchdProofs.prAct_eq`); its db step `Ci.prWatchApply` takes gh's answer as an argument and was not stated; P1/P2 over fair runs need that step, the monadic poll and `GhChecks`/`GhState` |
| PrWatch: `fair_of_stall`, `not_P*_of`, `getD_*`, `tk_*`, `agt_*`, `preach*` | not applicable | refutations with a switch off and the model's lemmas (`PrWatch.lean` itself stays: Decide.lean imports it) |
| Workspaces: `W1_of`, `W2_of`; Real: `landedRef_reach`, `sweepGate_W1`, `wtRemove_only`, `delRef_guarded`, `endAgent_keepsGit` | moved | on `RecM`, the code run on a machine that records each command (Assumptions.lean): `SweepProofs.sweep_W1` (every `worktree remove` the sweep runs passed `Gate` on the calls before it), `sweepGate_W1` (a worktree that passed `Gate` is listed and there, has no process inside, is clean, was not used in the last 30 min, and its HEAD is reached from a protected ref or its directory is gone), `landed_reach_spec`, `landedRef_reach_spec`, `wtRemove_only`, `delRef_guarded`, `endAgent_keepsGit` (W2); end to end over any run of sweeps and ends, branch deletes included: `SweepProofs.no_work_lost` |
| Workspaces: `replay_W`, `gitTick_gcOk` | not moved | the model's replay instance and its GC step; the code's sweep is the one `sweep_W1` is about |
| Workspaces: `W3_of`, `orphan_ev`, `agent_ev`, `ends_tick`, `reusable_ready`, `finished_reap` | not moved | W3 is liveness over fair runs on top of W1 and the agents' behaviour |
| Workspaces: `W4_of`, `B1_of` | not moved | `Workspaces.baseOut` and the per-task bases are monadic over git |
| Workspaces: `not_W*`, `forever_of_loopOk`, the rest | not applicable | refutations with switches off, the model's frames |
| Comms: `C1_of`, `C1all`, `cinv_*`, `comms_replaced`, `tick_binds_none` | not moved | `ensureComms` is monadic over hc (terminals, spawn); the takeover step is moved (`WatchdProofs.bind_changed`, `bind_ok`) |
| Comms: `not_C1_*`, `creachable_of_run`, `set_*`, `foldl_fix`, `wd_frame`, … | not applicable | refutations and the model's world |
| Restart: `R1a_of`, `R1a'_of`, `R1b_of`, `R1c_of`, `restart_ticks`, `wdinv_*` | not moved | the watchd record and tick lease check the other watchd's pid outside their transaction (PORT.md), so (a) needs that check moved inside or `Kill0Alive` on a recording world; (b), (c) are liveness of real processes |
| Real: `reap_gone`, `restart_alive`, `waiter_alive`, `lapsed_stays` | not moved | each pairs a tool's answer with the model's view (`HcLsLive`, `HcRunStarts`, `Kill0Alive`, `NowMono`): the assumptions are now named, but the code's reads are monadic (`hcTerminals`, `pidAlive`) and no theorem ties them yet |
| Real: `prAct` | moved | `WatchdProofs.prAct_eq` |
| Real: `engine_step`, `engine_reach`, `serializable`, `stmt_out`, `busyClean`; Iso: all; Sql, SqlParse | not applicable | the Lua's sqlite use as an engine model; the code's store is `Store.txn` (one `BEGIN IMMEDIATE` transaction per command) and assumes `Atomic`. Iso's `migrate_ok` (db.connect's migration): not moved, `Real.connect` is unproved |
| Cut: `passesIndep_of` | moved | `WatchdProofs.guard_ok` (a pass that fails ends alone) |
| Cut: `N1cut_of`, `Q1cut`, `tickCut_*`, `lifecycleCut_*`, `replay_cut` | not moved | invariants of a tick cut partway need the tick as steps; the tick is monadic. Each db step a pass commits is a transaction of `Cross.XCmd` (end, reaps), whose invariants hold after any prefix: `Cross.run_xinv` |
| Cut: `not_passesIndep`, `stuck36`, `seq_reap0`, `tickCut_none` | not applicable | refutations without `passGuard` |
| LoopSafe: `iteration_safe` (R2) | moved | `WatchdProofs.guard_ok` |
| LoopSafe: `loop_safe` | not moved | `Cmd.Watchd.loop` is `partial`; each turn is `guard` (`guard_ok`) and `Sys.sleep` |
| Env: the hypotheses, `consistent`, `sqlite_consistent` | moved | `Assumptions.lean`: each tool hypothesis on the code's calls (`AncestorReach` … `GhState`; `HcLsShows`, `Kill0Finds` are one direction of `HcLsLive`, `Kill0Alive`), the five sqlite ones as `Atomic`; `consistent` |
| Trust: `need_sweep_*` | moved | `SweepProofs.need_sweep_*` (Proofs/Trust.lean): for each of `sweepGate_W1`'s six tool assumptions, a machine with the other five on which a worktree passes `Gate` and the guarantee fails |
| Trust: the other `need_*`, `i_*`, `nudge_enabled` | not moved | their theorems (`landedRef_reach`'s and the hc and process ones) are not stated on the code with the same hypotheses, or not moved |
| Checkers: `*_spec` | not applicable | the model's Bool checkers against its Props |
| Contract: all | as their family above | restatements over the model's types (each row above covers its Contract name) |
| Findings: all | not applicable | the model's counterexample runs; each fix is built into the code. Findings in the port: S3's lock by an ended agent (fixed, `Locks.lock`), `Msgs.wakes` asking `cold` for an urgent row (fixed), N1 (1) with `idleJob` (by design; the model's N1 now says it, board #125): PORT.md |
| Exists: `lasso_run`, `fair_run_exists` | not applicable | non-vacuity of the model's fair runs; the code's run statements take any run |
| example/Client.lean | not applicable | a downstream proof of Contract.lean |

CI: `.github/workflows/swarm-lean.yml` runs `./check.sh` on Linux and checks the launcher runs the binary. The hpl
build needs `../../../high-perf-lean`, outside this repo, so it runs locally only (`./check.sh` builds it when that
checkout has an hpl binary).

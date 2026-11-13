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
Spawn's reservation finds fewer live agents than the max, auto-spawn's claim takes only the pool's top, and a failed
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

## What the proofs assume

All of it is in `SwarmLean/Assumptions.lean`, each a definition a theorem takes as a hypothesis (none is an axiom).
`Audit.lean` prints, for each, the theorems that take it.

| Assumption | About | Says | Taken by |
|---|---|---|---|
| `Atomic` | SQLite | processes' transactions that ran at once apply one after another in some order (stands for swarm/model's five sqlite hypotheses: the code's every write is one `BEGIN IMMEDIATE … COMMIT`) | 13 theorems: `one_winner`, `exactly_one_winner`, `one_winner_all`, `atomic_good`, `exactly_once_atomic`, `atomic_inv`, `shown_once`, `shown_for_it`, `cursor_passes_only_shown`, `atomic_ran`, `end_atomic`, `reap_atomic`, `atomic_xinv` |
| `AncestorReach` | git | `merge-base --is-ancestor ref b` exiting 0 means `b` holds `ref`'s changes | none yet (#115) |
| `SameContentReach` | git | `diff --quiet ref b -- <files ref changed since the merge base>` exiting 0 means the same | none yet (#115) |
| `StatusClean` | git | an empty `status --porcelain` means nothing uncommitted | none yet (#115) |
| `ListedOn` | git | a worktree `worktree list` lists is there | none yet (#115) |
| `WtRemove` | git | `worktree remove` takes a clean worktree away and nothing else, refuses a dirty one | none yet (#115) |
| `DelRef` | git | `update-ref -d refs/heads/b k` deletes `b` only if its tip is `k`, nothing else | none yet (#115) |
| `HcLsLive` | hc | `hc ls --json`, when it answers, lists a terminal live exactly when it is | none |
| `HcKillEnds` | hc | `hc kill h` ends `h` and leaves the repo | none (#115: W2) |
| `HcSendTargets` | hc | `hc send h l` types `l` into `h` alone, starts or ends no terminal, leaves the repo | none |
| `HcRunStarts` | hc | `hc run --json --bg` that exits 0 started the terminal and pid it prints | none |
| `Kill0Alive` | OS | `kill(p, 0)` is 0 exactly when `p` is in the process table | none |
| `CwdsProc` | OS | `Machine.cwds` lists a directory inside every worktree a process sits in | none (#115) |
| `TouchedRecent` | filesystem | a worktree used in the last 30 min has an mtime within 30 min | none (#115) |
| `NowMono` | clock | `Clock.now` never goes back | none |
| `GhChecks` | gh | the verdict `Ci.verdict` reads off a listed PR is its checks' state | none |
| `GhState` | gh | a listed PR not closed is MERGED when merged, else OPEN | none |

`consistent`: a machine on which no command runs has every tool assumption, so they are jointly satisfiable; that the
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
| End: `endOther_git` | not moved | that the end touches no worktree needs `hc kill`'s effect (`HcKillEnds`) on a world that records commands: board #115 |
| End: `endOther_force`, `not_N1end_force*` | not applicable | `--force` skips the check by design |
| NoWorkLost: `N1_of`, `replay_N1`, `finished_of_holds`, `lifecycle_keeps`, `reapTask_keeps`, `lifecycle_tk` | moved | (1) as the model now states it: a stalled job (a sleep loop or a hung tree, `idleJob`) is not work (#106's finding, board #125: the model's `bgStall`; `hungStep_hung` on the code; `idleJob`'s loop itself is not proved). Moved: `fate_end_free`, `endStep_free`, `keeps_bg`, `keeps_iff`, `reapTask_spec`, `reap_atomic`. (4), W1's part: not moved, #115 |
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
| Workspaces: `W1_of`, `W2_of`, `replay_W`, `gitTick_gcOk`; Real: `landedRef_reach`, `sweepGate_W1`, `wtRemove_only`, `delRef_guarded`, `endAgent_keepsGit` | not moved | the sweep decides in a monadic loop from git's answers; "it removes only a clean, landed, unused worktree" needs a world that records the commands run, with the git assumptions (now named in Assumptions.lean): board #115 |
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
| Trust: `need_*`, `i_*`, `nudge_enabled` | not moved | they show each tool hypothesis of Real.lean's theorems is needed; no Lean theorem takes a tool assumption yet, so there is nothing to show needed |
| Checkers: `*_spec` | not applicable | the model's Bool checkers against its Props |
| Contract: all | as their family above | restatements over the model's types (each row above covers its Contract name) |
| Findings: all | not applicable | the model's counterexample runs; each fix is built into the code. Findings in the port: S3's lock by an ended agent (fixed, `Locks.lock`), `Msgs.wakes` asking `cold` for an urgent row (fixed), N1 (1) with `idleJob` (by design; the model's N1 now says it, board #125): PORT.md |
| Exists: `lasso_run`, `fair_run_exists` | not applicable | non-vacuity of the model's fair runs; the code's run statements take any run |
| example/Client.lean | not applicable | a downstream proof of Contract.lean |

CI: `.github/workflows/swarm-lean.yml` runs `./check.sh` on Linux and checks the launcher runs the binary. The hpl
build needs `../../../high-perf-lean`, outside this repo, so it runs locally only (`./check.sh` builds it when that
checkout has an hpl binary).

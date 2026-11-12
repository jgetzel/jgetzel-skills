# A Lean model of the swarm's coordination

`SwarmModel/Model.lean` models what `swarm/lua/swarm` does to coordinate agents: the board (tasks and their
`--after` dependencies), leases and watchd's reaping and auto-spawn, locks, agents, and inboxes. It is plain
Lean 4 with no dependencies: one `State`, one function per command or event, and `Reachable`, the states any run
can reach. The five safety properties are theorems about every reachable state, for any number of agents, tasks,
locks and messages. Every bug the model found is a run that Lean evaluates. Random runs are replayed through
the real CLI against a scratch `swarm.db`, so a model that drifts from the code fails a test.

It replaces the Quint model of board task #107 (branch `sr-92/quint-model`, never merged), whose TLC checks
covered two agents and at most three tasks and mostly didn't finish: *Results* compares the two.

| File | What it is |
|---|---|
| `SwarmModel/Model.lean` | the model: state, actions, `step`, `Reachable`, `run`, and the properties as functions |
| `SwarmModel/Frame.lean` | which fields of the state each change leaves alone |
| `SwarmModel/Basic.lean` | induction over reachable states; S2 and S5 |
| `SwarmModel/Glob.lean` | locks.lua's lock patterns lifted (`tokens`, `one`, `meet`, `covers`, `overlaps`), the glob semantics `gm`, and what they are: `covers_iff`, `overlaps_iff` (board #26) |
| `SwarmModel/Locks.lean` | S3, and `noSharedFile_of_reachable`: S3 as files |
| `SwarmModel/Inbox.lean` | S4, and `tick_inv`: a property every part of watchd's tick keeps is kept by the tick |
| `SwarmModel/Workers.lean` | S1 |
| `SwarmModel/Findings.lean` | the counterexamples as runs (and findings #16 and #17, lassos; #18 to #21, W1-W4 on the current `Cfg`; #28, #29, Sp1-Sp2; #30, #31, P1-P2, stalls), and the same runs with the fix on |
| `SwarmModel/Liveness.lean` | L2 and L4 in one state: `idleClaim_not_stuck`, `deadLive_not_stuck` |
| `SwarmModel/Fair.lean` | fair runs (`Run`, `Run.Fair`) and L2 over them: `idleClaim_leads_to` |
| `SwarmModel/Taken.lean` | L1 over fair runs: `startable_taken` (and `claimable_taken`, `ready_step`, `tick_ready`, `lifecycle_fills` it is built from); board #53's stop stays lifted once lifted (`stopped_step`, with `stop_kept`, `grow_step` and the invariant `SK`) |
| `SwarmModel/Boot.lean` | L3, the reopened half: `booting_reads` (with `bootFirst`, a spawned holder reads the answer at its first turn) |
| `SwarmModel/Workspaces.lean` | W1-W4 and B1 (sw-bases) as statements, refuted with the fix's switch off (`not_W1_branch`, `not_W1_proc`, `not_W2`, `not_W3_formal_wt`, `not_W3_formal_agent`, `not_W4`, `not_B1`) and proved with it on (`W1_of`, `W2_of`, `W3_of` over fair runs, `W4_of`, `B1_of`; `replay_W`: all five of `replay`); `forever_of_loopOk` makes a two-state loop a fair `Run` |
| `SwarmModel/NoWorkLost.lean` | N1 (board #15) as a statement, refuted with each fix's switch off (`not_N1_bgKeeps`, `not_N1_retake`, `not_N1_allWts`, `not_N1_bgLives`, `not_N1_ownAdded`) and proved with them on (`N1_of`; `replay_N1`) |
| `SwarmModel/Comms.lean` | the communicator: several swarms (`World`, each swarm a `State`), hc terminals with a Herdr space, each swarm's communicator row, its watchd record (meta.watchd, a pid), meta.watchd_up and the watchd processes, and a `--restart` waiting for the one it started (`CCfg`, `cstep`, `CReachable`); C1 and `C1all` as statements; `tick_binds_none`; C1 proved with the fix on (`C1_of`, via `CInv`) and its liveness half over fair runs (`CRun`, `CRun.Fair`: `comms_replaced`). The refutations (`not_C1_shared`, `not_C1_dead`, `not_C1_space`, `not_C1all_fixed`) are in `Findings.lean` |
| `SwarmModel/Restart.lean` | `swarm watchd --restart` (board #49): R1 (a), (b), (c) as statements (`R1a`, `R1b`, `CRun.FairWd`), the invariant `WdInv` (`wdinv_of_reachable`), `R1a_of`, `R1b_of` (with `waitUp`), `R1c_of` and `restart_ticks` over fair runs; the refutation without board #41's handover, `not_R1b` (finding #34), is in `Findings.lean` |
| `SwarmModel/Spawn.lean` | spawn reservation and launch failure (board #16): `SWorld` (the `State` and auto-spawn's backoff, failures and halt), the tick whose launch fails, `rollbackAll`; Sp1-Sp3 (`Sp1_of`, `Sp2_of`, `Sp3_of`) |
| `SwarmModel/PrWatch.lean` | PRs and the wait on their checks (board #28): `PWorld` (tasks, each with its PR: opened, checks pending, green or red, merged, `told`; agents working or idle, staying, an urgent message unread), `pstep`, watchd's poll (`pollTask`), the switches `gated` (`ci.flow` is pr-gated), `wakeFix`, `closeFix`; fair runs (`PRun`, `PRun.Fair`); P1 and P2, refuted with a switch off by `stall` (`fair_of_stall`) and proved with it on (`P1_of`, `P2_of`; `main_P1`, `main_P2`) |
| `SwarmModel/Holder.lean` | L3, the holder half over fair runs: `holder_leads_to` (and `pa_step`, the per-action step lemma, and `unblock_pa`) |
| `SwarmModel/Gone.lean` | L4 over fair runs: `deadLive_leads_to` (and `Rz`, `rz_of_reachable`: with `racy = false` no agent is between a read and its write) |
| `SwarmModel/Exists.lean` | non-vacuity: `lasso_run` (a lasso whose cycle takes every fair action enabled in it is a fair `Run`) and `fair_run_exists`, a fair run of `replay` meeting L1-L3's side conditions |
| `SwarmModel/Answer.lean` | L3 over fair runs, one statement per task: `answer_reaches`; `L3I`, the invariant the halves took as hypotheses (`l3_of_reachable`); `owner_step` |
| `SwarmModel/Traces.lean` | writes random runs of the `sreplay` instance (`replay` with auto-spawn's launch failures) as JSON, and the scripted runs (`script`; `P.script`, PrWatch.lean's) |
| `SwarmModel/GlobCases.lean` | writes random lock patterns and paths with Glob.lean's answers, for `locks_model_spec.lua` |
| `../../lua-lean` | the Lua semantics, parser, translator and program logic, a package of its own the model requires (`lua-lean/DESIGN.md`): `LuaLean/Interp.lean` the semantics (board #28), `Shallow.lean` the translator's target and `tools/Lift.lean` the translator (board #31), `Hoare.lean` `RunP` (board #39); the CLI `lua-lean/lua-lean` |
| `SwarmModel/LuaCases.lean` | writes random chunks with the interpreter's results, for `luasem_spec.lua`: lua-lean's, and calls of util.lua, locks.lua and difflib.lua |
| `SwarmModel/LockSrc.lean` | locks.lua and util.lua as syntax trees (`gen-lock-src.sh`, with `lua-lean dump`) |
| `SwarmModel/Lifted/Locks.lean`, `Tasks.lean`, `Watchd.lean` | locks.lua and tasks.lua lifted, and watchd.lua's `M.iterate` (`--only`), built by `check.sh` |
| `SwarmModel/LoopSafe.lean` | R2 (board #67): no Lua error escapes an iteration of watchd's loop (`iterate_safe`), with `Ok`, a run that ends in no Lua error, and its rules for the shallow combinators |
| `lift.sh [--check \| --all]` | writes `Lifted/` with `lua-lean lift`; `--check`: fails if it is stale; `--all`: lifts every module and checks each proof (`lua-lean prove`) |
| `SwarmModel/Env.lean` | the environment (board #34): every assumption about git, hc (`hc_run_starts`: `hc run --bg` starts the program, board #49), gh (`gh_checks`, `gh_state`, board #28), processes, files and the clock, as `Tools` (what the swarm runs) and one named axiom each about `real`; `consistent`: an ideal machine has them all. And sqlite's (board #33): `Db`, `realDb`, one axiom per kind of op (`sqlite_begin`, `sqlite_read`, `sqlite_write`, `sqlite_commit`, `sqlite_rollback`); `sqlite_consistent` |
| `SwarmModel/Real.lean` | the Lua's decisions on the tools' answers are the model's on its view, for any `Tools` given the assumptions each names as hypotheses (`Tools.landedRef_reach`, `Tools.sweepGate_W1`, `Tools.wtRemove_only`, `Tools.delRef_guarded`, `Tools.endAgent_keepsGit`, `Tools.reap_gone`, `Tools.restart_alive` (`--restart`'s new watchd is alive as the model's `restart` makes it), `Tools.waiter_alive`, `Tools.lapsed_stays`, `Tools.prAct`: ci.pr_act on gh's answers); a run of any db with sqlite's assumptions is a run of `Iso.lean`'s engine (`Db.engine_reach`, `Db.serializable`, `Db.stmt_out`, `Db.busyClean`); and each for `real` and `realDb` from Env.lean's axioms, under its old name: `landedRef_reach`, `sweepGate_W1`, `wtRemove_only`, `delRef_guarded`, `endAgent_keepsGit`, `reap_gone`, `restart_alive`, `waiter_alive`, `lapsed_stays`, `prAct_real`, `realDb_reach`, `real_serializable`, `real_stmt_out`, `real_busyClean` |
| `SwarmModel/Release.lean` | H2, the user's or the communicator's release of a task another agent holds (board #45): `releaseOther_spec`, `releaseOther_enabled`, `deliver_released`, `stop_read` and `released_reads` over fair runs; finding #32 (`not_S1_humanRelease`), the run in which it breaks S1 without board #53's fix; L1 over fair runs, `startable_leads_to`, with `stop_lifts` (the stop lifts for good) |
| `SwarmModel/End.lean` | H1, `swarm end` by the user or the communicator (board #46): `endOther_spec`, `endOther_enabled`, `finished_eq` (its check is lifecycle's but the 2 min), `N1end_of` (it ends no agent that holds work), `endOther_git`, `endOther_force` (`--force` is `leave`); finding #33 (`not_N1end_force`), the forced end of an agent mid-job |
| `SwarmModel/Away.lean` | `swarm away` and `--back`, and the notice watchd sends the communicator for a block (board #47): Q1 (`Q1_of`; finding #35, `not_Q1`), A1 (`away_keeps`, `tick_keeps_blocked`, `back_questions`), A2 (`A2quiet_of`, `not_A2quiet`; `A2live_of` over `Run.CommsFair`, `not_A2live` on a fair run), A3 (`A3`, a frame theorem of the tick), A4 (`away_twice`, `back_twice`, `since_kept`, `back_digest`, `questions_sorted`, `digest_done`, `digest_ended`); `side_step`, what each step does to the communicator's side |
| `SwarmModel/Nudge.lean` | `swarm nudge` as the action `hnudge` (board #50): N1' (`N1'_frame`, a frame theorem: the step is the state unchanged; `Env.Tools.N1'` and `Env.N1'_real` with `hc send` as `HcSendTargets`), `hnudge_enabled`, `hnudge_reachable` |
| `SwarmModel/Stay.lean` | stays and watchd's liveness check of a stayer as actions `stay`, `endStay`, `stayCheck`, `stayHung` (board #79): `stayer_kept`, `tick_keeps_stayer`, `endOther_stay`, `stay_spec`, `endStay_spec`, `endStay_enabled`, `stayCheck_spec`, `stayHung_spec`, `digest_hung` |
| `SwarmModel/Contract.lean` | the theorems to build on downstream (board #25), restated over the model's types: *Using these proofs downstream* |
| `example/Client.lean` | a proof downstream, importing only `Contract.lean`: a toy client, and an assumption discharged for `Env.ideal` |
| `SwarmModel/Iso.lean` | sqlite's isolation as the code uses it (board #33): the engine (`Eng`, `step`, `Reach`), `serializable`, `stmt_out`, `busyClean_of` and `not_busyClean_deferred`; db.connect's migration, `migrate_ok` and `not_migrate_ok`; `sqlLang`, Sql.lean's statements as the engine's |
| `SwarmModel/Decide.lean` | the Lua's pure decisions lifted (board #27): watchd's `keeps` and `fate`, msgs' `wakes`, ci's `pr_act` (board #28), each proved the model's (`keeps_lifted`, `fate_lifted`, `fate_end`, `fate_reuse`, `wakes_lifted`, `prAct_lifted`), and the gap `keeps_gap`; H1 (board #46): `swarm end`'s check, `end_why` (`endWhyL`, `endWhy_lifted`, `endWhy_of_fate`); F1 (board #41): fate's recorder, what `state --json` reports (`fateRec`, `report_lifted`, `fateRec_vals`, `fateRec_all`, `fateRec_short`) |
| `SwarmModel/DecideCases.lean` | writes random inputs with Decide.lean's answers, for `decide_model_spec.lua` |
| `Audit.lean` | `check.sh`'s gate: the axioms each theorem rests on; fails on any but Lean's three and Env.lean's |
| `SwarmModel/Sql.lean` | the SQL the Lua hands sqlite, as a semantics: values with storage classes and affinities, tables, `exec` of one statement on a connection (board #29) |
| `SwarmModel/SqlParse.lean` | a statement's text to `Sql.Stmt`: lexer and parser for that subset; `claimWrite`, `task claim`'s write, evaluated by the kernel |
| `SwarmModel/SqlCases.lean` | writes random cases of every statement with `Sql.exec`'s answers, for `sql_model_spec.lua` |
| `sqlcases.json.gz` | 5340 of those cases (20 per statement, seed 29) the Lua suite runs |
| `../lua/test/sql_inventory.lua` | every SQL statement in `swarm/lua/swarm`, read from the source (310 sites, 264 statements) |
| `check.sh` | builds the model, which checks every theorem and run, then runs `Audit.lean`; fails on `sorry`, `native_decide`, an axiom outside Env.lean, or one with no case in `env_spec.lua` or `sqlite_spec.lua` |
| `replay.sh [n] [steps] [seed]` | `n` fresh runs, each replayed through the CLI |
| `traces/*.json.gz` | 12 runs of 50 steps (seed 107) and 19 scripted runs the Lua suite replays (`script-away`: board #47's; `script-nudge`: board #50's; `script-stay`: board #79's; `script-pr-*`: PrWatch.lean's, through a fake `gh`; `script-restart-*`: Restart.lean's, real watchd processes held at a fake `hc ls`) |
| `globs.json.gz` | 3000 of those cases (seed 26) the Lua suite checks |
| `../lua/test/cli_model_spec.lua` | the replay: one test per trace |
| `luasem.lua.gz` | 3000 of those chunks (seed 28) the Lua suite runs under LuaJIT |
| `../lua/test/luasem_spec.lua` | each chunk under LuaJIT must give the Lean interpreter's results (`lua-lean/test/luasem.lua`) |
| `../lua/test/env_spec.lua` | each of Env.lean's assumptions against the real tool, by its name (hc's three with `SWARM_TEST_HC=1`, gh's two with `SWARM_TEST_GH=1`: this repo's latest PRs, `gh pr list` against GitHub's REST API and git) |
| `../lua/test/sqlite_spec.lua` | Env.lean's sqlite assumptions against real sqlite through db.lua, many processes at once |
| `decide.json.gz` | 3000 cases each of keeps, fate, wakes and pr_act (seed 28) the Lua suite checks |
| `../lua/test/decide_model_spec.lua` | watchd.keeps, watchd.fate, msgs.wakes and ci.pr_act against Decide.lean's on each case |
| `../lua/test/locks_model_spec.lua` | locks.lua's `tokens`, `covers` and `overlaps` against Glob.lean's on each case, and `gm` against fnmatch on the tame ones |
| `../lua/test/sql_model_spec.lua` | each case through db.lua on real sqlite, against Sql.lean's answer; and the cases' statements are exactly the inventory's |
| `lakefile.toml`, `lean-toolchain`, `lake-manifest.json` | Lean 4.35.0, no packages |

## The model

One value holds the whole state; every watchd tick is a pure function of it, composed as the Lua composes it
(`reapTasks`, `reapLocks`, `lifecycle`).

- **Tasks** are absent, open, claimed, blocked, done or dropped, with an owner, `--after` dependencies, a lease
  (live or lapsed), evidence (empty or not), and the unblock answer if any. Agents claim, renew, release, block,
  finish (`done --evidence`) and drop their own; the communicator adds (`--after`), changes dependencies
  (`task after`, cycles refused), unblocks with an answer, and drops any task.
- **Leases** lapse as time passes (`expire`). Reap reopens a lapsed claim by the rule of the release being
  modelled (`release`, below) and tells the owner.
- **watchd's lifecycle**: an idle agent past 2 minutes with no claim or lock is ended, unless its context is
  small and the pool has work: then it is *reusable*, and gets a digest message once per new pool id. With no
  reusable agent, watchd spawns into free slots (up to the roster), one per startable task, and the new agent's
  first turn reads its task.
- **Locks** are patterns; `swarm lock` refuses a pattern that has a file in common with a live lock of another
  agent (`locks.covers`, tabulated for the model's patterns). Locks lapse and are reaped.
- **Agents** are working, idle, blocked (an hc permission prompt) or ended, with or without a live waiter (the
  Stop hook's `swarm wait`), small or big context, cold or not (idle past the prompt cache with a big context), staying
  or not (`swarm stay`: lifecycle keeps it, `swarm end` refuses it; the text is outside the model).
  An agent's slot is reused by the next spawn after it ends (the Lua gives that agent the next name; the replay
  maps slots to names).
- **Dead terminals**: `die` ends an agent's terminal with no `swarm leave`: its row stays as it was (it reads as
  live), it has no waiter, and it does nothing more (`dead`). Watchd's reap ends such a row (`reapGone`: the same as
  `leave`) only if watchd runs (`Cfg.watchd`), `hc ls` answers (`hcSees`: else `live_addrs` is nil) and the row has an hc
  address (`unbound` lists the slots without one). `swarm who` and `swarm post` split rows by `hc ls` at read time, so
  they show a dead row gone even with no watchd; that does not change the row, which the model keeps as live.
- **Messages** are one log with a cursor per agent. A hook, `swarm read`, a wake, a boot and the end of an hc
  prompt deliver every unread message. The waiter wakes the agent on an urgent message, or on any message if
  the agent isn't cold.
- **Git** (`Git`, one field of the state): worktree slots (`Cfg.nwts`), branches and commits. The main checkout is
  outside the model. A worktree is there or not, has a branch checked out, a HEAD, is dirty (an untracked file) or not,
  has a process inside or not, and was touched in the last 30 min (`recent`) or not. Branches are `Cfg.nbases` bases
  (0 is `main`; the rest, e.g. `formal`, exist from the start) and one per worktree slot (`<name>/w<w>-<k>` in the
  replay). A commit holds its ancestors and its content, a set of patches: an ordinary commit adds one fresh patch (a
  new file), a squash merge holds the union. So the Lua's `landed_ref(HEAD, main)` (an ancestor, or the same content
  under other commits; `gh` isn't modelled) is "every patch of HEAD is in main" (`Git.onMain`), and `landed` adds
  "clean". An agent's git commands (`GitOp`, one action `git a op`, only while working): add a worktree (its directory
  is named after the agent: `own`, with the slot's generation, is `owned_wts`), edit in it (the Edit hook sets
  agent.wt), commit, land (`git push . HEAD:<base>`, a fast-forward, refused while the base is checked out anywhere),
  squash-merge into a base, check out a base or the worktree's own branch. A second worktree only after an edit, so
  `wt_map`'s branch fallback has one candidate. The world (`world w op`): 30 min pass, a process moves in or out.
- **watchd and git** (`gitTick`, in `tickOf`): `unlanded` (lifecycle keeps an idle agent) is work not on `main` in the
  worktree `wt_map` picks (agent.wt, else the one with its branch), or since PR #123 in any it owns, its recorded one
(`rhead`) too. `sweep_worktrees`
  removes a worktree no live agent's agent.wt or `wt_map` names, with no process inside, untouched 30 min, clean and
  landed; `end_agent` removes the ended agent's `wt_map` worktree unless a live peer's agent.wt is it, if it is clean
  (git refuses a dirty one), whatever process is inside. Both then `branch -D` the branch it had checked out, unless it
  is `main`: a base like `formal` goes too. The base is `main` everywhere: `nbases > 1` is the swarm that lands elsewhere.
- **The communicator's inbox and the user's away flag** (board #47): what watchd and the CLI send the communicator
  (`cbox`: a block's notice, `swarm away`'s line, `--back`'s message; its other messages are outside the model) and how
  far it has read (`ccur`, moved by `commsRead`: a hook or `swarm read`); `away` (meta away, since a point of `evs`), and
  `digest` (meta away_digest). `evs` is the event log the digest reads (`task block`, task-blocked, done, an agent's
  end). The tick's last part is the notice loop (`notices`): a blocked task whose latest question wasn't told is told
  (urgent unless away) and marked told; `hcPrompt` sends its own "is blocked" notice and marks the task told.
- `believes` (the tasks an agent thinks it holds), `seen` (what each agent was shown), `pend` (answers not yet
  read by the task's holder) and `early` are ghosts: they exist for the properties.

The agents' choices are free (any command, in any order) with one assumption from the brief: an agent with a
small context, no claim and work in the pool takes work before it stops. Agents run a command only with an empty
inbox: the PreToolUse hook delivers before every one.

Each fix the model found or confirmed is a switch of `Cfg`, so the model records the code before and after it:

| Switch | Before | After |
|---|---|---|
| `release` | `ended`: 624cf79 keeps a lapsed claim while its owner is live | `notWorking`: b04cf08 (PR #110) reopens it unless the owner is working; `idle`: edffafc (PR #111) only when the owner is idle |
| `answerOnTask` | the unblock answer is only a DM | PR #110 stores it on the task |
| `claimChecksDeps` | `task claim`'s write checks only `state='open'` | PR #112 checks the dependencies in the write |
| `evidenceRequired` | `done --evidence ""` is accepted | PR #113 refuses it |
| `lockOverlap` | `lock` refuses only a pattern covering the other | PR #114 refuses any common file |
| `lockForms` | covers takes a glob as a directory too (`m/?` covers `m/?/x`), but overlaps leaves that form out, and the pattern as a literal path; it reads `[!]a]` as the class `[!]`, and a `?` or `*` meets any class, two classes always | board #26: a glob is only a glob; overlaps compares every form, classes by the bytes they match, and reads classes as covers does (`Glob.overlaps_iff`) |
| `deliverCas` | a delivery's cursor write ignores a delivery in between | PR #115 writes only from where it read |
| `passedOver` | a reusable agent holds spawn back forever | PR #116 ends one that passed the work over |
| `waiterAlive` | an idle agent whose waiter exited is kept reusable, and never reads its digest | PR #119 ends it |
| `bgKeeps` | reap reopens a lapsed claim of an idle owner even while its background job runs | PR #121 keeps it |
| `retake` | the 350k fence on `task claim` refuses a task reap took from that very agent | PR #121 lets it retake (`reaped`, the Lua's `reaped_from`) |
| `allWts` | lifecycle keeps an agent only for the one worktree `wt_map` picks | PR #123 keeps it while any worktree it owns is unlanded |
| `uncleanNudge` | an idle agent kept only by an unclean worktree is kept silently, forever | PR #122 sends one urgent nudge per idle stretch |
| `perTaskBase` | the landed checks (lifecycle, sweep) ask main only | sw-bases, board #3 (in the Lua, `bases.lua`): lifecycle asks the bases of the tasks an agent owns (`abases`; `Cfg.taskBase` gives each task's, main if none), the sweep every base a task names and main (`pbases`); `B1`, `B1_of`, finding #22 |
| `splitGC` | end_agent removes the ended agent's worktree, looking at no process; sweep runs `branch -D` on whatever was checked out but main | sw-bases, board #4: ending kills the terminal only; the sweep checks reachability from a protected ref itself and deletes only a branch that is no base and is reachable |
| `recordedWorkspaces` | an agent may check out a base in its worktree | sw-bases, board #5: swarm creates and records worktrees; a checkout of a base is refused; a spawned agent's `wt_map` and `owned_wts` read its record alone (`Agent.recorded`), not the worktrees it adds |
| `bgLives` | lifecycle ends an idle agent with no claim while its background job runs (reap looks at the job since PR #121, lifecycle never did), and the job dies with the terminal | board #15: lifecycle keeps it while the job runs (`machine.bg_agents`); `swarm end` refuses it without `--force` |
| `ownAdded` | lifecycle reads a spawned agent's worktrees from its record alone, so one it added itself and left unlanded doesn't keep it | board #15: lifecycle's `unlanded` reads the record and the worktrees named after the agent |
| `stopFirst` | the user's release of a working agent's task lets a peer claim it before the ex-owner reads the stop (finding #32) | board #53: the task records the stop; claim, the pool and auto-spawn refuse it while the ex-owner is at work and hasn't read it |
| `renotify` | watchd marks a block's notice sent by any task-blocked event with the same question, so the same question asked again (by the same agent after an answer, or by another after a release) is never told (finding #35) | board #47: sent only by a task-blocked event after the task's latest `task block` (`toldAfter`) |
| `awayQuiet` | (the feature off) a block's notice is urgent while the user is away | `swarm away`: not urgent while away |
| `backTells` | (the feature off) `--back` sends the communicator nothing | `--back`: one urgent message naming the questions that wait |

All three are in the Lua (boards #3 to #5) and on in `replay` (tasks 2 and 4 on `formal`); W1 to W4 hold with them (board #6).
`bgLives` and `ownAdded` are in the Lua and on in `replay` too; N1 holds with them (board #15).

The communicator's world (`Comms.lean`) has its own switch, `CCfg.ensureComms`:

| Switch | Before | After |
|---|---|---|
| `ensureComms` | `swarm join` refuses only a live binding of the same row elsewhere; reap ends a communicator row whose terminal is gone and nothing binds a new one; auto-spawn opens tabs in the space of watchd's own terminal | board #9: watchd's tick launches a communicator in the swarm's space when the swarm has work and none is bound to a live terminal there whose session is it; auto-spawn launches into the swarm's space; `join` refuses a terminal outside the swarm's space, and one that is another swarm's communicator unless `--takeover` |

In the Lua (board #9); C1 holds with it (`C1_of`, board #10).

| Switch | Before | After |
|---|---|---|
| `waitUp` | a watchd whose record another holds exits at once | board #41: it exits only once that one runs and meta.watchd_up names it, takes the record back from a dead one, and else waits; `--restart` reports success only then |

In the Lua (board #41); R1 (b) holds with it (`R1b_of`, board #49), and fails without it (finding #34).

`racy` splits two commands into the read and the write the Lua does separately: `task claim` (the dependency
check, then the update) and the waiter's delivery (unread, then the cursor). The waiter's write ends with the
turn it starts, whose prompt hook delivers whatever is still unread.

`Cfg` also has the sizes: agent slots, the roster, tasks, lock patterns. The theorems hold for every `Cfg`
with the fix's switch on; the log is unbounded. `replay` (4 slots, 4 tasks, 4 patterns, `racy` off) is what the
replay drives.

## Properties

Each is a sentence, then the function in `Model.lean` that says it of one state.

Safety:

- **S1** No task has two agents at work on it: no two agents, each working or at an hc prompt, both believe they
  hold the same task. `oneWorker`. Proved with `humanRelease` off or `stopFirst` on: without board #53's fix the user's
  release of a working agent's task breaks it (finding #32)
- **S2** No task is claimed while a task it is after isn't done. `noEarlyStart`
- **S3** No two live locks of different agents cover a common file. `locksDisjoint` (with `overlap`, which is
  exactly "a common file": `Glob.overlaps_iff`; `noSharedFile_of_reachable` says it of every path)
- **S4** No message is shown twice, and no cursor passes a message it didn't show. `inboxExact`
- **S5** Every done task has evidence. `doneHasEvidence`

Liveness, under fairness (the actions of `fair` in `Findings.lean`: watchd ticks; leases lapse and idle agents
age; a waiter with a message it wakes on wakes; a spawned agent boots; an hc prompt is answered; a working agent
reads its messages and takes work):

- **L1** A startable task doesn't stay startable forever while a slot is free. Its negation in one state, for a task
  `t`: `startable s t ∧ slotFree c s`. (Of the pool, "some task is startable", `idleSlot`, it is false: finding #16.)
- **L2** A claimed task whose owner is idle is eventually done or open again, unless its owner gets back to
  work. `idleClaim`
- **L3** An unblock answer eventually reaches whoever holds the task, unless the task ends. `answered`. False in the
  model with `bootFirst := false`: a spawned agent is reaped before its first turn, over and over (finding #17).
  `bootFirst` (a boot beats a lease, as in the Lua: a fresh 2 h lease, a boot in seconds) is on by default
- **L4** A row whose terminal is gone is eventually ended (its claims and locks released). Its negation in one state:
  `deadLive`. Fairness: watchd ticks, and an `hc ls` that lists the terminal as gone. `watchd := false` (no watchd), a
  failing `hc ls`, and an unbound row each break it (findings #14, #15). Proved over fair runs: `deadLive_leads_to`

PRs (board #28; `PrWatch.lean`, a layer of its own: tasks, their PRs and checks, agents that stay, watchd's poll, under
its own fairness: watchd polls, a waiter with an urgent message wakes, a working agent reads, CI finishes):

- **P1** In a repo whose `ci.flow` is pr-gated, an agent that stays idle for its PR's checks does not stay idle forever
  once they are green: it is woken. `waitsGreen` (idle, staying, owning the claimed task, its PR open and green, not told).
  Refuted with `wakeFix` off (finding #30), proved with it on (`P1_of`)
- **P2** In every flow, a task whose PR is merged does not stay claimed forever. `mergedClaimed`. Refuted with `closeFix`
  off (finding #31), proved with it on (`P2_of`)

Workspaces (sw-bases; `Workspaces.lean` states each as a `Prop`). The protected refs are the bases (`Cfg.bases`: main,
and a swarm's own such as `formal`); `Git.safe` is reachability from one, checked the way workspace GC must check it
(an ancestor, or the same content under a squash), never by `git branch -d`:

- **W1** A worktree is removed only if it is clean, unattached (no live agent's agent.wt or `wt_map` pick), no process
  is inside and its HEAD is reachable from a protected ref; a deleted branch is no protected ref and its tip is
  reachable from one. `gcOk`, of each step
- **W2** Ending an agent removes no worktree and deletes no branch: a tick does to git only what the sweep does.
  `endKeepsGit`
- **W3** On a fair run from a reachable state no worktree stays an orphan forever (there, clean, on a protected ref,
  unattached, no process, untouched 30 min: `orphan`), and no agent stays idle and free with its task's work on that
  task's base forever (`doneOnBase`: staying for nothing (board #79: `idleFree`; a stayer is kept until its stay ends),
  no background job running, and the worktree `wt_map` picks and every one it owns
  clean, its HEAD on a base of a task it owns, main if none)
- **W4** No worktree has a base checked out, so landing on a base is never refused for it. `noBaseOut`

Each fails with its fix's switch off (findings #18 to #21) and holds with it on, for every instance: `W1_of`, `W2_of`
(`splitGC`), `W4_of` (`recordedWorkspaces`) of every reachable state, and `W3_of` (`perTaskBase` and `splitGC`) over
fair runs. W1 and W2 need no invariant: a step other than the tick only adds worktrees and moves branches forward, and
with `splitGC` the tick's git is the sweep's (`gitTick_gcOk`: what it removes was swept, the branch it deletes no base
and reachable). W3's orphan half: the tick sweeps an orphan, so it is enabled while one stays, and fairness takes it
(`orphan_ev`). The agent half (`agent_ev`), from "idle with its work on its bases forever": with `perTaskBase` that is
lifecycle's `finished`, and reap keeps it so (`finished_reap`). A tick then ends the agent (`ends_tick`: ended, or its
slot a new agent's), or, the agent reusable, leaves it ready (`reusable_ready`: waiter armed, an unread digest), so the
tick is enabled wherever the agent's `wake` (`wakeRead` with `racy`) is not. Strong fairness takes the wake, or
`reapGone` for a dead row, and either ends the idle stretch. W3 also takes PR #116 and #119 (`passedOver`, `waiterAlive`),
watchd, and `hc ls` seeing every row (`hcSees`, `unbound = []`): a reusable row whose terminal is gone is woken by
nothing else.

The user's release (board #40, #45; `Release.lean`). `swarm task release N` by the user (the panel's `human`) or the
communicator of a task another agent holds is the action `releaseOther` of `step` (the communicator's actions have no
actor, as `unblock` and `drop`, so the user and the communicator are one action; `humanRelease`, on as in main, switches
it). So S2-S5, N1, W1-W4 and L1-L4 above are proved with it in `step`; S1 is with board #53's fix (`stopFirst`), and
without it is refuted (finding #32).

- **H2** The user's release of a task another holds, claimed or blocked (by `task block` or an hc prompt), is always
  enabled (`releaseOther_enabled`); afterwards the task is open with no owner and no hc prompt, the ex-owner is sent an
  urgent `.released` stop, and nothing else on the board, no agent and no cursor changes (`releaseOther_spec`); a
  delivery that shows the stop drops the ex-owner's belief that it holds the task, as for reap's (`deliver_released`);
  an answered hc prompt does not take the task back. Liveness: on a fair run from a reachable state the ex-owner does
  not keep at work unaware of the stop forever: it reads it (its cursor passes it), or stops being at work, or its
  terminal is gone, which L4 then ends (`stop_read`, `released_reads`). No switch refutes H2 (the stop is there or the
  feature is not); what it refuted is S1.
- **Stop first** (board #53, `stopFirst`): the release records its stop on the task (`stopTo`, `stopMsg`; the Lua's
  `stop_to`, `stop_msg`), and while the ex-owner is at work (working, or at an hc prompt) and hasn't read it the task is
  `stopped`: `task claim` refuses it (in the write's transaction), and it is out of the pool, so auto-spawn and digests
  skip it. An ex-owner not at work holds nothing back: every way back to work delivers the inbox first. S1 holds with it
  (`oneWorker_of_reachable`); a belief may now rest on the unread stop of an open task (`HS` in `J`;
  `Contract.s1_believes_held_stop`). L1 holds with it: on a fair run the stop lifts (`stop_read`: the ex-owner reads it
  or stops being at work; a dead terminal is excluded, as for L1) and, while no one releases the task again, stays
  lifted (`stopped_step`): `stop_lifts`, `startable_leads_to`.

The user's end (board #40, #46; `End.lean`). `swarm end A` by the user or the communicator (watchd.cmd_end;
`agents.in_charge` gates who, so, as `releaseOther`, it is one actorless action) is `endOther a force` of `step`, so S1-S5,
N1, W1-W4 and L1-L4 above are proved with it in. It ends the row as `leave` does (its claims and locks released, the
terminal killed and the waiter with it); with `--force` it is `leave` (`endOther_force`). The liveness statements that
take a run with no `leave` take one with no `swarm end` too (`startable_leads_to`, `claimable_taken`; a forced end of a
booting holder for `booting_reads`): an agent the user ends can't be waited for. L3 (`answer_reaches`) needs nothing:
an end of the holder frees the task, as a `leave` does.

- **H1** Without `--force`, `swarm end A` makes lifecycle's checks but the 2 min idle, whoever runs it: idle, no stay, no
  claim, no lock, no background job, no work off its tasks' bases (`endable`; lifecycle's `finished` is `endable` and the
  2 min, `finished_eq`; the Lua's check is `watchd.end_why`, over fate's own reads, lifted as `Decide.endWhyL` and proved
  the model's: `endWhy_lifted`, and whatever fate would end or reuse it ends, `endWhy_of_fate`). It is enabled exactly
  then (`endOther_enabled`), and it changes nothing but A's row: no task, lock, message, cursor, git ref or other agent
  (`endOther_spec`). So it ends no agent that holds work (`N1end`, the N1 of `swarm end`: `N1end_of`, on PR #123's
  `allWts`, board #15's `ownAdded` and per-task bases), and, forced or not, it removes no worktree and deletes no branch
  (`endOther_git`): what an ended agent leaves in a worktree only GC may remove, and W1 says GC removes nothing unlanded.
- **`--force`** is the user's explicit choice to lose work: `N1end c true` is refuted (finding #33: `not_N1end_force`, an
  agent mid-job, whose job end_agent's cgroup.kill kills; `not_N1end_force_wt`, one with an uncommitted file, which stays
  in its worktree). The same runs without `--force` are refused.

Away and back (board #40's item (d), board #47; `Away.lean`). `swarm away`, `swarm away --back` and the communicator's
read are actions of `step` (`awayOn`, `back`, `commsRead`), and the block notices are part of the tick and of `hcPrompt`,
so S1-S5, N1, W1-W4 and L1-L4 above are proved with them in.

- **Q1** Every block reaches the communicator: after a tick, the latest question of every blocked task was told (a
  task-blocked event after its latest `task block`, logged with its notice). `Q1_of` with `renotify`; refuted without it
  (finding #35, `not_Q1`): the same question asked again is never told. The replay of `script-away` fails on the old Lua.
- **A1** Away loses no question: away, back and the communicator's read change no task, agent, lock, message, cursor,
  git ref or event (`away_keeps`); the tick, away or not, leaves a blocked task blocked with its owner and question
  (`tick_keeps_blocked`); `--back`'s digest lists exactly the blocked tasks (`back_questions`). No switch refutes it.
- **A2** While away no block notice to the communicator is urgent, and otherwise each is (`A2quiet_of`; refuted with
  `awayQuiet` off, `not_A2quiet`). Liveness: on a run where the communicator's waiter wakes it on an urgent message it
  hasn't read (`Run.CommsFair`), everything sent to it before `--back`, the questions asked while away among it, is read
  (`A2live_of`, with `backTells`); without the back message a fair run leaves the question unread forever (`not_A2live`).
- **A3** Non-interference: the away flag changes no staffing decision: the tick with the flag set to anything ends where
  the tick with it as it is ends (reap, spawns, ends, digests, git, events), but for the notices' urgency (`A3`, a frame
  theorem: `blind (tickOf c (withAway s v)) = blind (tickOf c s)`). No switch refutes it (no code reads the flag there).
- **A4** Away and back are idempotent: a second away is refused and keeps the first since (`away_twice`, `since_kept`),
  `--back` when not away is refused (`back_twice`); back's digest is the events since away (`back_digest`): the questions
  oldest first by their latest question event, then id (`questions_sorted`), the tasks done since and still done
  (`digest_done`), the agents ended since (`digest_ended`), and the agents hung since and not ended since (`digest_hung`,
board #79). The Lua reads these by event id after the away event's
  (board #74), as the model by index in `evs`, so what happened in away's own second before it is not since. The replay
  runs each away and back twice.

Nudge (board #50; `Nudge.lean`). `swarm nudge a` is the action `hnudge a` of `step` (not watchd's unclean `nudge`):
enabled for a live agent with a terminal (the CLI refuses an unknown, ended or unbound one: `hnudge_enabled`), and the
state unchanged, since the CLI writes only a nudge event and types a line, neither of which the model keeps. The line's
effect on the agent is its own `prompt`, already a step. It is not in `fair`, so S1-S5, N1, W1-W4 and L1-L4 above are
proved with it in `step`.

- **N1'** A nudge changes no task, claim, lock, lease, message or cursor (`N1'_frame`: `step c s (.hnudge a) = some s'
  → s' = s`), and its `hc send` types the line into that agent's terminal and no other, starts or ends no terminal and
  leaves every worktree, branch and commit (`Env.Tools.N1'`, from `HcSendTargets`; `Env.N1'_real`). The replay
  (`script-nudge`, and random steps) checks the db unchanged but for the one nudge event, and that hc's last call was
  `send <that agent's terminal> <the line>`. A roster agent joined outside hc has no terminal in the replay, which the
  model's `replay` instance (no `unbound`) doesn't have: the replay binds it for that command only.

Stays (board #79; `Stay.lean`). `swarm stay "<what>"` and `swarm stay --end`, the agent's own (`stay a on`, while working),
`swarm stay --end A` by the user or the communicator (`endStay a`, actorless as `releaseOther`; refused unless A is live and
stays), and watchd's liveness check of an idle stayer are actions of `step`: `Agent.stay`, and per idle stretch `checked`
(a `stay-check` sent) and `hung` (a `stay-hung` logged), both cleared by `stop` as the Lua's events older than last_active
stop counting. `stayCheck a` is watchd.hung's periodic check: an idle stayer, 50 min idle (the model's `stale`), not cold,
its waiter alive, not checked yet, is sent the check (`.check`, not urgent, a message that wakes); `stayHung a`, the check
unanswered LIVENESS_WAIT later (the agent still idle, its waiter alive), logs `Ev.hung a` and tells the communicator,
urgent, once. Both are the environment's (time passing, an agent that does not answer), not in `fair`, so S1-S5, N1,
W1-W4, L1-L4, H1, H2 and A1-A4 above are proved with them in `step`. `idleFree` reads the stay (fate's first check), so
`finished`, `reusable`, `ends`, watchd's unclean `nudge`, `doneOnBase` (W3) and `swarm end`'s `endable` do.

- **St1** Lifecycle keeps a stayer: it is not finished, so neither ended nor reused (`stayer_kept`), and the tick leaves
  a live stayer's row as it was but for the pool ids a digest told it of (`tick_keeps_stayer`); `swarm end` without
  `--force` refuses it (`endOther_stay`; `Decide.endWhy_lifted` and `fate_lifted` read the row's stay). The stay
  commands change the flag alone (`stay_spec`, `endStay_spec`, `endStay_enabled`).
- **St2** The liveness check goes to an idle stayer once per idle stretch, and only one with a live waiter that is not
  cold (`stayCheck_spec`); unanswered, its hang is logged and the communicator told, urgent, and not again in that
  stretch (`stayHung_spec`).
- **St3** `--back`'s digest lists as hung exactly the slots whose agent hung since away and has not ended since
  (`digest_hung`: of the slot's hung and ended events since away, the last is a hung; agents.digest's `stay-hung`
  events after the away event's, of an agent row not ended, a slot's next agent being another row).

The replay (`script-stay`, and random steps) runs the commands and, for `stale`, `stayCheck` and `stayHung`, moves
last_active (30 min; 51 min, past LIVENESS_IDLE and short of COLD_IDLE) or the check event (400 s) back and runs a tick:
`Traces.lean` offers the check and the hang only where the model's tick changes nothing, `stale` only for a stayer, and
neither `cool` of a stayer nor `endStay` of an idle agent 30 min idle with unlanded work (watchd's tick would check the
first and nudge the second). Watchd's quiet notice is outside the model: the replay marks it sent before each tick.

No work lost (board #15, `NoWorkLost.lean`):

- **N1** watchd never discards work that isn't landed. Four parts (`N1`): (1) the tick leaves every agent that holds work
  as it was, but for the pool ids a digest told it of (`keptBy`): not ended, its slot not given to a spawn, its job,
  agent.wt and worktrees its own still. An agent holds work (`holdsWork`) when it is live and its background job runs, or
  a worktree it works in (`wt_map`) or owns is dirty or has its HEAD on no base of a task it owns (main if none). (2) Reap
  never reopens a claim whose live owner's job runs: after the tick the task has that owner still. (3) An agent reap took a
  task from may claim it back until another agent does: the 350k fence doesn't refuse it. (4) W1: GC removes a worktree or
  branch only if clean and reachable from a protected ref.

N1 fails with any of five switches off, each a finding (#10 `bgKeeps`, #11 `retake`, #12 `allWts`, #26 `bgLives`, #27
`ownAdded`; `not_N1_bgKeeps` and the rest) and holds with all of them on, for every instance (`N1_of`, which also takes
`release = .idle`, `perTaskBase` and `splitGC`). No invariant is needed: with the fixes lifecycle calls no agent that holds
work finished (`finished_of_holds`), so it neither ends nor reuses it, and a spawn fills only a slot that isn't live
(`lifecycle_keeps`); a claim reap keeps is still held, so lifecycle leaves the task alone (`lifecycle_tk`).

What N1 does not say. Its tasks' bases are those of the tasks the agent owns once reap has run: an idle owner with no job
loses a lapsed claim to reap (it is told, and may retake it), and if its worktree is clean with its HEAD on main but not
on that task's base, the same tick ends it. The commits are on main, a protected ref, and the task is open again.
An agent's own `leave` and the reap of a dead terminal (`reapGone`, whose job died with it) end agents too; N1 is about
lifecycle and GC. A job that never ends keeps its idle agent forever (W3 takes `bgEnd` as fair).

The communicator (`Comms.lean`). The model above is one swarm with an anonymous communicator; C1 needs several swarms
(one per repo db) sharing hc terminals, so `World` holds a `State` per swarm, the terminals (live or dead, a Herdr space,
the swarm whose communicator the session is: its `SWARM_NAME`, ListAgents name and the db its `swarm wait` reads), each
swarm's communicator row (the terminal meta.comms's row is bound to) and its watchd (the terminal it was started from).
Actions: any action of a swarm's model but its tick; a terminal opens in a space; `join [--takeover]` from a terminal;
watchd started from a terminal; a terminal dies (and the watchd started from it, the communicator's background Bash);
watchd's tick of a swarm (reap of a dead communicator row, the model's `tickOf`, spawns placed in watchd's terminal's
space).

- **C1** Whenever watchd ticks a swarm, the state it leaves, if the swarm has a live agent or an open task, has exactly one
  live communicator: the row meta.comms names, bound to a live terminal in the swarm's own space whose session is that
  communicator (reachable by its ListAgents name; its `swarm wait` reads this swarm's inbox). And every live agent was
  launched in that space. `c1` of `tickW`, for every reachable state where watchd runs: `C1`

C1 is said of the state each tick leaves, not of every state (`C1all`): a terminal can die between two ticks, and no fix
makes the death and watchd's next look at it one step, so `C1all` is false with the fix on (`not_C1all_fixed`). It is
also conditional on watchd running: who restarts a dead watchd is board #18. C1 fails three ways on the current `CCfg`
(findings #22 to #24, proved: `not_C1_shared`, `not_C1_dead`, `not_C1_space`).

With `ensureComms` C1 holds (`C1_of`). Every reachable world keeps a state and a communicator row per swarm, and the
spaces agents were launched in never change, since every launch is into the swarm's own space (`CInv`,
`cinv_of_reachable`); the tick binds a fresh terminal at home in session when the swarm has work and none is there. The
liveness half: on a run fair to watchd (a swarm whose watchd runs at infinitely many steps is ticked at infinitely many:
`CRun.Fair`), from a reachable world, a swarm whose watchd keeps running has its communicator again at some step after
any step, however often it dies (`comms_replaced`). Who restarts a dead watchd is still board #18.

`swarm watchd --restart` (`Restart.lean`, board #49). In Comms.lean's world each swarm's watchd is a record (meta.watchd: a
pid, an index into the watchd processes, each with its swarm, its terminal, running or not, has it ticked, has it written
the record) and meta.watchd_up. `watchd i x` starts one by hand from terminal x (refused while the record's watchd runs);
`tick i` is the record's watchd's tick, and its first writes watchd_up. A tick claims meta.watchd_tick (board #71), in
one transaction with the read of the record, and gives it back at its end: `tick i` waits while another running watchd
holds it, and claims it again for the watchd's next tick; `tend p` ends the tick p claimed before another took the record
(p's tick runs, then the claim is given back); a start, takeover or take-back claims it when it is free. Board #41's
restart is five actions:
`restart i x` (`hc run --bg` starts `swarm watchd --takeover <recorded flags>` in the hidden terminal x: Env.lean's
`HcRunStarts`; refused with no record; one restart of a swarm at a time), `takeover p` (the new watchd's start writes the
record, whoever it names), `rpoll i` (the restart reads a record other than the one it started with), `rok i` (success:
that one holds the record, runs, and watchd_up names it) and `rfail i` (it died, or 90 s passed: kill it, give the record
back where it still holds it). `crash p` is a watchd's death; `die x` ends the processes in terminal x and leaves the
record naming a dead pid, as meta does. `loop p` is the loop of a watchd, not mid-tick, whose record another holds. The
recorded flags
change nothing a takeover does here: the new watchd's tick is the old one's `tickW` (`--comms` is resolved into them, and
`--max-agents`, left out, would only rewrite the auto-spawn number, which `Cfg.roster` fixes).

- **R1** (a) At most one watchd ticks a swarm: the record's, running, and it is that swarm's (`R1a_of`, of every reachable
  world). (a') No two ticks of a swarm overlap: a step that runs a watchd's tick (`tick i`, `tend p`) finds no other
  watchd mid-tick (holding meta.watchd_tick and running), and one mid-tick keeps its claim until a step runs its tick
  (`R1a'_of`, of every step). (b) Never zero once there was one: the loop ends a watchd only when the record names another that runs, that
  watchd_up names and that has ticked; `--restart` reports success only then (`R1b_of`, with `waitUp`). (c) On a run fair to
  the ticks (`CRun.Fair`) and to the watchds' own steps (`CRun.FairWd`: a takeover, loop or tend step enabled at
  infinitely many steps is taken at infinitely many), a watchd that keeps running gets its swarm ticked at infinitely many steps
  (`R1c_of`); so does the one a restart starts (`restart_ticks`).

(a) is structural: the record is one slot. Before board #71 the Lua's loop read the record and then ticked, so a takeover
between the two let the old watchd finish one tick beside the new one's first; now the read and the claim of the lease
are one transaction, and the new watchd's loop looks again every second until the old one's tick ends. (a') needs no
invariant: every claim is of a free lease. The replay of `script-restart-ok` holds the old watchd mid-tick across the
takeover and fails if the new one reaches its tick before `tend` (it does with the loop before board #71). (b) needs `WdInv`: the
record and watchd_up name processes of their swarm, watchd_up one that has ticked, a swarm with a process has a record,
and a restart's old record is a process of its swarm. Without `waitUp` (b) fails, finding #34 (`not_R1b`): the restart's new
watchd takes the record, the old one exits, the new one dies before its first tick, and no watchd runs. (c) holds either way:
if the record's watchd stops running, the one that runs is enabled to take the record over (its start) or back (its loop),
once the tick it claimed before, if any, ends (`tend`), and fairness takes each. `CRun.Fair` asks for ticks of a swarm
whose watchd runs at infinitely many steps; with the lease such a tick can wait for a `tend`, which `FairWd` takes. What R1 leaves out: a hand `--takeover` and `--once`; two restarts of one swarm at a time; pid reuse;
`--restart`'s 90 s as time (its failure may come at any step).

- **R2** No Lua error escapes an iteration of watchd's loop, on the real Lua (board #67). The loop's body is
  `M.iterate` (`swarm/lua/swarm/watchd.lua`). It calls `iteration` under `pcall` and returns the fresh results.
  `iteration` runs the pass (the record, then the tick), an error's report and the pause, each under its own `pcall`, so
  an error in one still leaves the others to run. `LoopSafe.iterate_safe`: a call of `M.iterate`, lifted by `lua-lean
  lift --only M_iterate` (`Lifted/Watchd.lean`), ends in no Lua error (`Err.val` or `Err.rt`). That holds for every
  oracle, every fuel and every argument, and for every value `iteration` holds, whatever it does when called: it may
  return any values, raise any value, change the heap in any way and call any effect. So it covers every behaviour of
  every call into hc, git, sqlite, re and io. It rests on one thing: the global `pcall` is the builtin, read from a `_G`
  with no metatable. That is how the semantics starts (`pcall_init`). If `M.iterate` is called with the pcall
  removed, the proof fails.

R2 does not cover a segfault, a hang (an effect that never returns), running out of memory, or a kill: the process
ends, or never comes back, without a Lua error. Restarting watchd is R1. A run that stops in the semantics (out of
fuel, an effect no oracle answers, a feature outside the subset) is not a Lua error either, so R2 says nothing about
it. Not proved: the lines of `iteration` between its pcalls, and the loop around `M.iterate` (`repeat … until why`,
then `util.die(why)` on purpose). Proving those needs a frame rule in lua-lean: a call leaves the cells it cannot reach
unchanged. Without one, a proof cannot trust a local read back after an arbitrary call, so `M.iterate` reads nothing
it held before the call. The frame rule is board #75.

Spawn reservation and launch failure (`Spawn.lean`, board #16). `swarm spawn --task N` reserves the name and the task in
one transaction (a row with no terminal, the task claimed for it), makes the worktree, then launches. `SWorld` is the
model's `State` with auto-spawn's meta rows: `backoff` (spawn_backoff's time is ahead), `bo` (the failed name the next
launch reuses, as the slot it was for), `fails` (spawn_fails) and `halt` (spawn_halt). Actions: the model's, but its tick;
watchd's tick with its launches working (`stick`: the model's spawns, drawn from the pool minus a halted task, none in a
backoff; a launch whose reused name a live row holds is refused, which auto_spawn counts as a failure); the tick whose
first launch fails (`fail`: launch.sh exits non-zero, or `raise`, launch_agent errors before running it); the backoff's
time passing (`lapse`). The fix is `rollbackAll`: undo the reservation on any failure, not only launch.sh's exit.

- **Sp1** A failed launch leaves nothing behind: the tick in which it fails ends where the same tick with no spawn ends,
  so no row of the failed agent and no claim of it remain. `Sp1_of`
- **Sp2** Right after a failed launch its task is startable: back in the pool at once, not when a leaked claim's 2 h lease
  lapses. `Sp2_of`
- **Sp3** On a fair run (the backoff's time passes: `lapse` enabled at infinitely many steps happens at infinitely many)
  a backoff lifts. `Sp3_of`

Sp1 and Sp2 fail with `rollbackAll` off (finding #28, `not_Sp1`, `not_Sp2`) and hold with it on, of every step. Sp3 holds
either way: the backoff is time. What the leak breaks after it is the next launch (#29). Not proved: that a halt only
lands on a task whose own launches failed (it needs "a slot whose launch failed stays not live until a spawn", over every
action); #29 is the run where it doesn't, with the switch off.

## Results

`check.sh` (`lake build`) checks everything below in about 12 seconds from nothing (16 s of CPU). No `sorry`,
no `native_decide`, no axiom beyond the three every Lean proof may use (`propext`, `Classical.choice`,
`Quot.sound`) and the environment's (`Env.lean`, only under `Real.lean`'s eight): `Audit.lean` collects each
theorem's axioms and prints the eight.

| Property | Theorem | Holds for every reachable state of every instance with | Quint + TLC, 2 agents |
|---|---|---|---|
| S1 | `oneWorker_of_reachable` | `release = .idle` (PR #111) | 883,023 states, 217 s |
| S2 | `noEarlyStart_of_reachable` | `claimChecksDeps` (PR #112) | stopped at 30 min, unfinished |
| S3 | `locksDisjoint_of_reachable`, `noSharedFile_of_reachable` | `lockOverlap` (PR #114), `lockForms` (board #26) | 4.05M states, 577 s |
| S4 | `inboxExact_of_reachable` | `deliverCas` (PR #115) | stopped at 30 min, unfinished |
| S5 | `doneHasEvidence_of_reachable` | `evidenceRequired` (PR #113) | 13.9M states, 625 s |

| Sp1, Sp2 | `Sp1_of`, `Sp2_of` (of each failing tick) | `rollbackAll` (board #16) | not checked |
| R1 (a), (b) | `R1a_of`, `R1b_of` | `waitUp` (board #41) for (b) | not checked |

Each theorem is for any sizes and any setting of the other switches, `racy` included. Sp3 (`Sp3_of`) is over fair runs
of the spawn layer, for every instance. A TLC run that finished
covered 2 agent slots, 1 to 3 tasks and a bounded log; the four that hit the 30-minute cap had seen 23M to 92M
states, and no liveness check got past the first instance.

What carries each proof:

- **S1**: an agent that believes it holds a task does hold it, or the task was dropped, or the agent isn't at
  work and has an unread `released` message for it; and no two agents have a belief that isn't of that last,
  stale kind (`J`). Reap under PR #111 reopens a claim only when its owner isn't at work, and tells it; every
  way back to work delivers the inbox first. It needs S4's "no cursor passes a message it didn't show", which
  holds with or without PR #115, and that `task add` never reuses an id (`Pfx`). The user's release (H2) is not of that
  kind: it tells an owner that may be at work; with board #53's fix (`stopFirst`) that owner's belief rests on the stop
  the task records, and no one takes the task until it is read or the owner stops (`HS`, `J_released`); without the fix
  S1 breaks (finding #32).
- **S3**: a lock's holder is live, and unexpired locks of different agents share no file (`LkInv`). As files:
  `overlaps_complete` (a path both cover makes `overlaps` true).
- **S4**: per agent, what was shown is in order and behind the cursor, everything behind the cursor since the
  spawn was shown, and the waiter's snapshot skips nothing between the cursor and its last id (`Inb`).
- **S2**, **S5**: the ghost flag stays off; done implies evidence.

Liveness: L1 (per task), L2, L3's two halves and L4 are proved over fair runs. A run is a sequence of steps (`Run` in `Fair.lean`); it is fair (`Run.Fair`) when
every action of `fair` that is enabled at infinitely many steps happens at infinitely many steps (strong
fairness; weak fairness is not enough for L1, see below). `idleClaim_leads_to`: in a fair run of an instance with
`racy = false`, `release ≠ .ended` (PR #110 or #111), `watchd`, the agent and the task in the instance, no `bgStart` or `die` in the run, and the agent with no job and a live terminal at the start, a state where an
idle agent holds a claim is followed by one where it doesn't: the lease lapses (`expire`), the tick reopens the task
(`tick_reopens`) or the owner gets back to work. A slot a spawn refills is a new agent: it boots at once (the proof
shows `boot` happens), so it doesn't count. The proof is two persistence lemmas (`persist`, `tick_persist`: while an
idle agent holds the claim, a lapsed lease stays lapsed and a booting agent keeps booting) and fairness of `boot`,
`expire` and `tick`. `racy` is left out: the race splits are for S2 and S4.

L1 is proved over fair runs too, **for each task** (`startable_leads_to`; the core is `startable_taken`). Take an
instance with `racy = false`, `watchd`, `passedOver` (PR #116), `waiterAlive` (PR #119) and `roster ≤ nagents`, a task
`t`, and a fair run that starts in a reachable state with no dead terminal and from there has no `leave`, `die`,
`waiterGone`, `reapGone` or `swarm end` (`endOther`) (an agent that leaves, dies or loses its waiter can't be waited for). Then some state of the
run has `t` not startable or no free slot: the task is taken (or finished, dropped), or a spawn fills the roster.
The proof, by contradiction from "`t` startable and a slot free forever":

- (`lifecycle_fills`) a tick that finds no reusable agent spawns for every pool task while the roster has room, so
  afterwards `t` is taken or the roster is full. So every tick fires with a reusable agent present, and a tick is
  enabled whenever there is none.
- (`reusable_ready`, `lifecycle_unread`) after a tick a reusable agent `a` is *ready*: idle, waiter armed, small context,
  not cold, and with an unread message (its `released`, or the digest the tick just posted). Where the tick is
  disabled, the same agent is ready already. Either way some agent is ready at infinitely many steps, so one agent `a` is
  (finitely many agents; `Cfg.agents`).
- (`ready_step`) a ready agent stays ready until it gets back to work, through every action but the four excluded: a
  tick doesn't end it (it is reusable), a delivery to someone else doesn't touch its cursor, a post only adds to its
  inbox. Its `wake` is enabled until then, so by fairness it wakes: working, inbox empty, small context.
- (`claim_enabled`) `claim a t` is then enabled, at infinitely many steps, so it happens, and `t` is taken.

Strong fairness is what makes the last two steps work: weak fairness lets two agents post to each other forever, so
neither's `claim` is continuously enabled. `Run.Fair` already is strong fairness. The invariants used are proved for every
reachable state (`i1_of_reachable`: there are `nagents` slots and cursors, only a big agent is cold; `inbInv_of_reachable`)
and kept by every action but `die` (`d_step`).

- (`booting_reads`, `Boot.lean`) L3, the reopened half. With `bootFirst`, a spawned agent that holds a task with an
  answer on it reads the answer at its first turn, unless it leaves, its terminal dies or the task is dropped: `keep`
  (any action but the tick, its boot and those) and `tick_keep` (a tick leaves a booting holder its claim: the lease
  is fresh, so reap passes it, and lifecycle neither ends nor replaces it) hold the claim, `boot` is fair, and
  `boot_reads` (the first turn's `takes`) clears the answer. Taken as hypotheses: the run is reachable, and
  `firstClaimed` is the task (a spawned agent holds one).
- (`holder_leads_to`, `Holder.lean`) L3, the holder half. While an agent holds the claimed task with its answer unread in its
  inbox (`Pa`; `unblock_pa`: an `unblock` of a live, non-booting owner establishes it), then in a fair run the holder reads it, or
  stops holding the task (reaped, ended, hc-blocked, done, dropped), or a spawned agent has the slot (`boot`, whose half is
  `booting_reads`). The step lemma `pa_step`: each of the 41 actions keeps `Pa` or ends it in one of those ways; `Pa` includes "the
  holder is live", so no separate invariant "held => live" is needed. A working holder's `readAll` and an hc prompt's `hcClear` are
  fair and deliver; an idle one is L2's (`idleClaim_leads_to`). Needs no `bgStart` or `die` after the start, none live at the start.
- (`deadLive_leads_to`, `Gone.lean`) L4. In a fair run of an instance with `racy = false`, `watchd` and `hcSees`, from a reachable
  state, an agent of the instance that is live with its terminal gone and not `unbound` is eventually not so: watchd's
  `reapGone` ends it (`endAgent`: its claims reopened, its locks freed), or something ends it first. No action is excluded from
  the run. `reapGone a` is in `fair` and stays enabled while the row is dead and live, because no agent is ever between a read
  and its write (`Rz`, `rz_of_reachable`: `claimRead` and `wakeRead` need `racy`); by fairness it fires. A dead row stays dead
  while live (a spawn takes only a slot that isn't live), so "not dead and live" means the row was ended. The three
  hypotheses are each needed: findings #14 and #15 (`deadLive_not_stuck` is the one-state form).

- (`answer_reaches`, `Answer.lean`) L3, joined: one statement about a task. From any reachable state of a fair run, an answer
  pending on task `t` is eventually read by whoever holds `t`, or `t` ends: done, dropped, or open again with nobody holding it
  (whoever takes it next reads the answer on the task as it takes it: `claim`'s `takes`, or a spawned agent's first turn, which
  the theorem covers again). Built from the invariant `L3I`, proved of every reachable state (`l3_of_reachable`, for `racy =
  false`, `answerOnTask`, `bootFirst`): a booting agent is idle with no waiter and holds at most one task, claimed with a live
  lease, so no spawned agent blocks a task before its first turn and `firstClaimed` is its task (`booting_fc`); whoever holds a
  task is live, so `unblock` finds its owner live and not booting (`unblock_owner`, the hypotheses of `unblock_pa`); and for a
  pending answer the holder is booting or has the answer unread in its inbox, and if the task is blocked it is an hc prompt the
  holder sits at. `owner_step`: a held task changes hands only in a tick, to an agent spawned for it. The proof: a booting
  holder boots (`keep`, `tick_keep`, `boot_reads`), unless it leaves or the task is dropped; otherwise the holder never changes,
  and it reads its inbox (`readAll` when it works infinitely often, `hcClear` when it sits at a prompt infinitely often), or it is
  idle holding the task claimed from some point on, which L2 (`idleClaim_leads_to`) says doesn't last. Same hypotheses on the run
  as the holder half: no `bgStart` or `die` after the start, none dead or running one at it.

Not proved: L1 for the pool (false, #16), L4 with `racy` (a dead agent's own `claimRead` would disable its reap; the model
lets a dead agent act, the code doesn't). With `bootFirst := false` L3 is false (#17).

Non-vacuity (`Exists.lean`): fair runs exist, so the theorems above are not true of nothing. `lasso_run`: a run from the
start that ends in a cycle (`lassoRun`: the cycle comes back to the state it left, and every fair action enabled at a state of
the cycle is in the cycle) is a fair `Run`. `fair_run_exists`: one on `replay` with every shipped fix on (task #1 added; agents 0
and 1 take turns claiming it, letting the lease lapse and releasing it), from the start, every state reachable, no dead
terminal and no background job at any state, and no `leave`, `die`, `waiterGone`, `reapGone` or `bgStart`: the side
conditions of `startable_leads_to`, `idleClaim_leads_to`, `holder_leads_to` and `answer_reaches` at every step (an `example` applies L1 to it).
With agent 1's claim left out the cycle is not fair (the check bites). It shows the
fairness and side conditions satisfiable together, not that L2's, L3's or L4's antecedent (an idle holder, an unread answer, a dead
terminal) occurs in a fair run: on this one both agents stay working.

## Findings

Every counterexample the Quint model found, and what fixed it. Each is an `example` in `Findings.lean`: the run,
with the fix's switch off, ends in a state that violates the property (`by decide`: Lean evaluates the run).
For a liveness property the run ends in a state where the property fails and no fair action is enabled, so a
fair run can stay there forever. The same run with the fix on is there too. Each was a real execution of the
Lua.

| # | Property | Switch off / what holds with it on | The counterexample | Fixed by |
|---|---|---|---|---|
| 1 | L2 | `release := .ended` / `idleClaim_not_stuck` | An owner goes idle holding a claim and nothing wakes it; its lease lapses, but reap keeps a lapsed claim while the owner is live, so the task stays claimed forever (task #106, seen live for ~6 h). | b04cf08, PR #110 |
| 2 | S1 | `release := .notWorking` / S1 | #1's first fix reopens a lapsed claim whenever the owner isn't working, including one stuck at an hc permission prompt; another agent claims it, the prompt is answered, and two agents work on the task. | edffafc, PR #111 |
| 3 | L3 | `answerOnTask := false` / the run | An unblock answer is only a DM. An idle owner that is cold isn't woken by a non-urgent message, so the answer never reaches it; reap reopens the task, and the agent spawned for it can't read the answer either. | b04cf08, PR #110 |
| 4 | S2 | `claimChecksDeps := false`, `racy` / S2 | `task claim` checks the dependencies, then a `task after` adds one that isn't done, then the claim's write (`where state='open'`) succeeds: a task starts before what it is after. | 58e9aa6, PR #112 |
| 5 | S5 | `evidenceRequired := false` / S5 | `task done --evidence ""` is accepted. | 89fe2a2, PR #113 |
| 6 | S3 | `lockOverlap := false` / S3 | `m/a*` and `m/*.lua` both match `m/a.lua`, but neither covers the other as a path, so both locks are granted. | cc63217, PR #114 |
| 7 | S4 | `deliverCas := false`, `racy` / S4 | The waiter reads the unread list, a hook delivers it and moves the cursor, the waiter writes its cursor and shows the same message again. | 5cdcb42, PR #115 |
| 8 | L1, L3 | `passedOver := false` / the run | A small-context idle agent was told of a task and went idle again without it; the task is open again with a free slot, and lifecycle keeps the agent reusable instead of spawning, so nobody takes the task or reads its answer. | 1ac83b1, PR #116 |
| 9 | L1, L3 | `waiterAlive := false` / the run | The same with a waiter that exited: the agent never reads the digest, so it stays reusable and holds spawn back. | aeaf44f, PR #119 (board #113) |
| 10 | N1 | `bgKeeps := false` / N1 (`not_N1_bgKeeps`) | An agent claims a task, starts a long background job (CI wait, model check) and stops; the lease lapses, reap reopens the task as its owner is idle, and watchd spawns a fresh agent onto it while the job runs (seen on #107). | PR #121 (board #115) |
| 11 | N1 | `retake := false` / N1 (`not_N1_retake`) | The task is reopened; its owner, whose context is past 350k, comes back and `task claim` refuses it, so only a fresh agent can take it. | PR #121 (board #115) |
| 12 | N1 | `allWts := false` / N1 (`not_N1_allWts`) | An agent owns two worktrees; `wt_map` picks the landed one, the other holds work not on main, and lifecycle ends the agent mid-task. | PR #123 (board #116) |
| 13 | stuck, silent | `uncleanNudge := false` / the run | An agent idle 30 min with an unclean worktree and nothing else holding it: no action is enabled, forever, and nobody is told. With the fix `nudge` is enabled and its urgent message wakes the waiter; a second nudge is refused until the agent has woken and stopped again. | PR #122 (board #114) |

Findings 10 to 12 refute N1 (`NoWorkLost.lean`), as do #26 and #27. #13 is a run only: no theorem says the nudge makes the agent clean (it can ignore it).
| 14 | L4 | `watchd := false` / `deadLive_not_stuck` | An agent holding #1 loses its terminal. With no watchd nothing ends the row: `swarm who` and `swarm post` show it gone, but it stays live, keeps its claim, and a message to it is stored unread. | open: run watchd, or end the row by hand (`swarm leave` is the agent's own) |
| 15 | L4 | `hcSees := false`, or `unbound := [0]` / `deadLive_not_stuck` | watchd runs but can't tell. The dead agent was working, so reap keeps its claim past the lease (`keeps`: the owner isn't idle) and #1 stays claimed forever. An unbound row is a communicator that joined from outside hc; `hc ls` failing makes `live_addrs` nil for every row. | open |
| 16 | L1 (the pool) | `idleSlot` / `lassoOk`, `periodic` | Two tasks, a free slot, one agent. It takes #1, stops holding it, the lease lapses, the tick reaps it: the agent is idle with an unread `released`, so `reusable`, and lifecycle does not spawn into the free slot. It wakes, takes #2, and the same again. Every fair action enabled anywhere in the loop happens in it, and a startable task and a free slot are there at every state. L1 holds of each task (it is taken over and over), not of the pool. Evaluated for 4 periods; one more period changes only the log, the cursor and what was shown (`periodic`). **Not the real watchd**: the loop needs every tick to come after the lease lapsed (a tick while the agent holds a live lease would spawn onto the other task), and watchd ticks every 30 s against a 2 h lease; the model lets fairness delay a tick that long. | not a bug |

| 17 | L3 | `!answered` / `lassoP`, `periodicD` | Two slots, one task. Agent 0 blocks #1, goes idle big and cold, and the answer to it is a DM it never reads. Reap reopens #1, the tick ends agent 0 and spawns a new agent into its slot for #1; the answer is stored on the task but only that agent's first turn (`boot`) reads it. Before it boots its lease lapses and the next tick reaps it and spawns into agent 1's slot; agent 0 now boots (it holds nothing), goes idle big, and the same happens the other way round. Every fair action enabled anywhere in the period happens in it (`boot` and `age` included), and #1 is never open at a state, so no `claim` is enabled: a fair run in which the answer is never read. Evaluated for 4 periods; one more changes only the log, the cursor, what was shown and where inboxes start (`periodicD`). With the period's agent booting before its lease lapses (`[.boot 0]`) the answer is read. **Not the real timing**: a spawned agent holds a fresh 2 h lease and boots in seconds, so the loop needs a launch that hangs for hours, every time; the model has no time between a lease and a boot. | `bootFirst`: a boot beats a lease (`booting_reads`); not a bug |

| # | Property | Switch off / what holds with it on | The counterexample | Fixed by |
|---|---|---|---|---|
| 18 | W1 | `splitGC := false` / W1 (`W1_of`) | Agent 0 lands its commit on `formal` and on main, checks `formal` out in its worktree and leaves. 30 min on the sweep finds the worktree clean, unused and on main, removes it and runs `git branch -D formal`: the swarm's base is gone (`not_W1_branch`; the replay's `script-sweep` is the Lua doing it). With `splitGC` the sweep removes the worktree and keeps `formal`. | fixed: board #4 (`splitGC` on in `replay`) |
| 18b | W1 | `splitGC := false` / W1 (`W1_of`) | end_agent looks at no process: agent 0's work is on main, a process sits in its worktree, it stops and ages, and the tick ends it and removes the worktree under the process (`not_W1_proc`). | fixed: board #4 (`splitGC` on in `replay`) |
| 19 | W2 | `splitGC := false` / W2 (`W2_of`) | By design today: the same run with no process. The worktree was touched within 30 min, so the sweep keeps it, but the tick that ends agent 0 removes it and deletes its branch (`not_W2`). With `splitGC` the tick ends the agent and leaves git alone. | fixed: board #4 (`splitGC` on in `replay`) |
| 20 | W3 | `perTaskBase := false` / W3 (`W3_of`) | A base that isn't main (the notapki `formal` swarm). Agent 0 lands on `formal` and leaves: its worktree is clean, unused, untouched, on a protected ref, and never swept, since the sweep asks main (`not_W3_formal_wt`). Or agent 0 claims #1, whose base is `formal`, lands it there, marks it done and goes idle: lifecycle asks main, so it is never ended (`not_W3_formal_agent`; if it goes stale, the unclean nudge wakes it once per idle stretch, forever). The fair run: agent 1 starts and ends a background job over and over, and no other fair action is enabled (`loopOk`, `forever_of_loopOk`). The replay's `script-formal` is the Lua keeping both. With `perTaskBase` the tick removes the worktree and ends the agent. | fixed: board #3, #4 (`W3_of`) |
| 21 | W4 | `recordedWorkspaces := false` / W4 (`W4_of`) | Agent 0 checks out `formal` in its worktree; agent 1's commit can no longer land on it (`git push . HEAD:formal` is refused while a worktree has it checked out) (`not_W4`). With `recordedWorkspaces` the checkout is refused. | fixed: board #5 (`W4_of`) |

| 22 | C1 | `ensureComms := false` / C1 (`C1_of`) | One terminal is the communicator of two swarms (2026-11-10: sk-comms and fm-comms both on t87, in the notapki space). fm-comms joins swarm 1 from t87, then sk-comms joins swarm 0 from the same terminal: bind looks only at swarm 0's own row. The session is sk-comms now, its `swarm wait` reads swarm 0's db, and swarm 1's notices are stored and read by no one; swarm 0's communicator also sits outside its space (`not_C1_shared`). With `ensureComms` the second join is refused, with `--takeover` too. | fixed: board #9 (`ensure_comms`, `join` checks, `SWARM_SPACE`), #10 (`C1_of`) |
| 23 | C1 | `ensureComms := false` / C1 (`C1_of`) | The communicator's terminal dies and the swarm runs on. Watchd runs from another terminal of the swarm's space; agent 0 blocks #1 and the communicator's terminal dies. The tick reaps its row, and no tick ever binds a new one (`tick_binds_none`), so the notice that #1 is blocked goes to a name no one reads (`not_C1_dead`). With `ensureComms` the tick launches a communicator in the swarm's space. | fixed: board #9 (`ensure_comms`, `join` checks, `SWARM_SPACE`), #10 (`C1_of`) |
| 24 | C1 | `ensureComms := false` / C1 (`C1_of`) | Watchd started from a terminal in another space spawns there: launch.sh opens the tab in the space of `HC_TERMINAL_ID`, which for auto-spawn is watchd's terminal (`not_C1_space`). With `ensureComms` the spawn lands in the swarm's space. | fixed: board #9 (`ensure_comms`, `join` checks, `SWARM_SPACE`), #10 (`C1_of`) |
| 25 | S3 | `lockForms := false` / the runs | covers takes `m/?` as a glob and also as a directory, so it covers `m/?/x`; overlaps leaves a glob's directory form out, so agent 1's `swarm lock m/?/x` is granted and the edit hook gives both agents `m/?/x`. With S3's exact `overlap`: overlaps also left out the pattern as a literal path and read `[!]a]` as the class `[!]`, so `[!]a]` and `b` (which share `b`) are both granted. The other way, it refused locks that share no file: a `?` met any class, even an empty `[z-a]`; two classes always met; a `*` met an empty class. With `lockForms` a glob is only a glob and overlaps is exact (`Glob.overlaps_iff`). | board #26 |

| # | Property | Switch off / what holds with it on | The counterexample | Fixed by |
|---|---|---|---|---|
| 26 | N1 | `bgLives := false` / N1 (`not_N1_bgLives`, `N1_of`) | Agent 0 starts a long background job (a build, a CI wait), stops holding no claim and goes idle. Lifecycle never looks at the job (only reap does, PR #121), so the next tick ends agent 0 and its terminal, and the job with it. With `bgLives` the tick keeps it until the job ends. | board #15 (`cli_lifecycle_spec`: `test_idle_agent_with_background_job_not_ended`) |
| 27 | N1 | `ownAdded := false` / N1 (`not_N1_ownAdded`, `N1_of`) | A spawned agent, whose worktree swarm recorded, adds a second worktree, edits in it, edits back in the first, lands that and marks its task done. The second holds an uncommitted file, but lifecycle reads a recorded agent's worktrees from its record and agent.wt alone, so the tick ends the agent. With `ownAdded` the worktrees named after it count too. The replay's `script-added` is the Lua keeping it. | board #15 (`test_recorded_agent_with_a_worktree_it_added_not_ended`) |
| 28 | Sp1, Sp2 | `rollbackAll := false` / Sp1, Sp2 (`Sp1_of`, `Sp2_of`) | A spawn's launch_agent raises before launch.sh runs (it can't write the agent's settings file: a disk full, a permission, the directory a test puts there), and cmd_spawn undid only launch.sh's exit. Agent 1 leaves, #1 is added, the tick's launch for #1 raises: slot 1's row is live with no terminal (status idle, `hc` null) and holds #1, which is out of the pool until its 2 h lease lapses and lifecycle ends the row (`not_Sp1`, `not_Sp2`; `test_spawn_task_raise_rolls_back`, and the replay at the fix's parent, `rollbackAll` off, 39 runs with raises agreed). With `rollbackAll` the raise is undone like the exit and the retry spawns for #1. | board #16: cmd_spawn runs everything after the reservation under one `pcall` |
| 29 | a halt is earned | `rollbackAll := false` / the run | The leak's knock-on: spawn_backoff keeps the failed name for the retry, and agents.reserve refuses a live row's name, which auto_spawn counts as a failed launch. Agents 1 and 2 leave, #1 and #2 are added, #1's launch raises (slot 1 holds #1); five times the backoff lapses and the tick's launch, for #2 now, is refused: auto-spawn halts #2, none of whose launches ran, and tells the communicator to spawn it by hand. A scripted replay of this run at the fix's parent (not kept: it is a run of the switch off) was the Lua doing it. With `rollbackAll` the first retry spawns both. | board #16 (as #28) |


| # | Property | Switch off / what holds with it on | The counterexample | Fixed by |
|---|---|---|---|---|
| 30 | P1 | `wakeFix := false` / P1 (`not_P1`, `P1_of`) | Seen four times on 2026-11-11 (ll-2 on PR #178, ll-3 on #180, ll-4 on #181, ll-6 on #182): an agent opens its PR, runs `swarm stay 'CI on PR #N, then merge'` and stops; the checks go green and nothing tells it. watchd's `--ci` polls the base's push runs, not PR checks, and agents are told not to poll `gh`. watchd's "ll-X did not wake on a message (#M)" was about a conflict notice, which by design never wakes (`msgs.wakes`), so the alarm was false and only the communicator's `hc send` moved the agent. The stall: agent 0 claims #1, opens its PR, stays and stops, CI goes green; watchd's poll is the one step and changes nothing, and no other fair action is enabled (`stall`, `fair_of_stall`). With `wakeFix` the poll posts an urgent message and the waiter wakes it (`script-pr-green`, `script-pr-red` are the Lua doing it). | board #28: `ci.pr_watch` in pr-gated repos; `hung` ignores notices |
| 31 | P2 | `closeFix := false` / P2 (`not_P2`, `P2_of`) | ll-3 merged #180 and never ran `task done`, holding its claim, so a task after it could not start. Agent 0 claims #1, opens its PR, merges it, stays and stops: #1 stays claimed while watchd polls. With `closeFix` the poll marks #1 done with the merge sha and tells the owner (`script-pr-merged`). | board #28: `ci.pr_watch`, every flow |

| # | Property | Switch off / what holds with it on | The counterexample | Fixed by |
|---|---|---|---|---|
| 32 | S1 | `humanRelease := true` (main, board #40) with `stopFirst := false` / S1 with `stopFirst` on, or `humanRelease` off (`oneWorker_of_reachable`) | Agent 0 claims #1 and works on it; the user (or the communicator) runs `swarm task release 1`: #1 is open and agent 0 is sent an urgent stop, which it reads only at its next tool's hook. Agent 1 claims #1 at once; both are at work and both believe they hold #1 (`not_S1_humanRelease`; the replay's `script-release` is the Lua doing it). | `stopFirst` (board #53): claim, auto-spawn and the pool refuse the task to others while the ex-owner is at work and hasn't read the stop; `script-release` now has agent 1 claim #1 after agent 0 reads it |
| 33 | N1 of `swarm end` | `--force` / `N1end` without it (`N1end_of`) | Agent 0 starts a long job (a build, a CI wait); the user runs `swarm end m-1 --force`: the row is ended mid-job and end_agent's cgroup.kill kills the job (`not_N1end_force`); or agent 0 has an uncommitted file and is ended (`not_N1end_force_wt`; the file stays in its worktree, `endOther_git`). Without `--force` both are refused. | not a bug: `--force` is the user's choice to lose work; `swarm end` without it refuses (board #40) |
| 35 | Q1 | `renotify := false` / Q1 (`not_Q1`, `Q1_of`) | Agent 0 blocks #1 and the tick tells the communicator; the answer comes, agent 0 reads it and blocks #1 again with the same question. watchd marked the notice sent by any task-blocked event of the task with that question text, so the second question was never told (nor another agent's same question after a release). Found by the model of board #47 and replayed (`script-away` fails on the old Lua) | board #47: a notice is sent once the task's latest question event is a `task block` (watchd.watchd_tick) |

Nothing else is open: every other counterexample above has a fix on main. #14, #15 and #32 are not fixed; #16 is a statement that is too strong, not a bug; #17 is the same for L3, and the model now says a boot beats a lease (`bootFirst`).

The notices to the communicator are not rows of the model, so "a notice for the communicator reaches a live one, or
its sender is told" is read from the code, not proved (C1 says a live one is there to read them after each tick): watchd posts its notices (`lease-late`, `blocked on #N`, idle
unclean worktrees, quiet) to the communicator's name, `msgs.post` stores them whether or not that row is live, and
only `swarm post` says anything of the recipient (`no terminal; can't be delivered now`, from `hc ls` at read time).
So a notice to a dead or unbound communicator, or posted before its terminal died, reaches no one and tells no one:
the same two causes as #14 and #15, and the sender of a notice is watchd.

## What is proved, what is replayed, what isn't modelled

**Proved**: S1 to S5, as *Results* says, of the model (S1 with `humanRelease` off or board #53's `stopFirst` on, finding #32), H2 (`Release.lean`) and H1 (`End.lean`). A proof is about `Model.lean`; that the model is the code
is what the replay tests. **Evaluated**: the counterexamples and their fixed runs. L1, per task, L2, L3, per task, and L4 are proved as statements about fair runs, for `racy = false`, and `fair_run_exists` shows fair runs meeting their side conditions exist. P1 and P2 (board #28) are proved over `PrWatch.lean`'s fair runs.

**Replayed** (random, not exhaustive): that the model is the code. Each step of a run does the command it stands
for (`task claim`, `lock`, `post`, `hook stop`, `swarm wait`, `watchd --once`, …) or, for time and the world,
writes the db (`lease_until` in the past, `last_active` back 200 s or 4000 s, `ctx_tokens`, the waiter's pid:
the test's own while the model's waiter is alive, none once it is gone), and then the db must match the model:
every task's state, owner, live lease, evidence and answer; every agent's status; every lock; every message to
an agent, in order; and each agent's unread list. The git steps run git in the fixture's repo (its main checkout
detached, a `formal` branch), and after them and every tick git must match too: every worktree there or not, its branch,
HEAD, `git status` clean or not and its mtimes (what sweep reads); every branch's tip; each live agent's agent.wt. A
process inside is a `sleep` started there; 30 min is an mtime set back. The 12 committed runs (seed 107, 50 steps) and
six scripted ones (`script-end`: a squash-merged worktree is landed by content, its agent ended and the worktree and
branch removed; `script-sweep`: a fast-forwarded one its agent no longer edits in swept with its branch, a dirty one kept;
`script-formal`: worktrees on main and on `formal` swept, the idle agent whose last worktree is on `formal` only, and who
owns no task, kept; `script-base`: an agent whose task's base is `formal` kept until its work is there; `script-spawned`:
a worktree a spawned agent adds and leaves swept while it works, since `wt_map` picks its recorded one; `script-added`: a
spawned agent kept by an unlanded worktree it added itself, by the tick that ends idle agent 1; `script-retry`,
`script-raise`, `script-halt`: a failed launch and its backoff, a raise undone, five failures halting a task and the halt
lifted once it is claimed; `script-release`: H2; `script-end-user`: H1, the communicator's `swarm end` of an idle agent
holding nothing, then `--force` of a working one, whose task the tick gives a new agent) are in the Lua suite; `replay.sh 60 40` does 60 fresh ones in about 2 minutes. The runs are of
`sreplay` (Spawn.lean): `failExit` is a tick with the fake launch.sh failing, `failRaise` one whose next agent's settings
file is a directory (so launch_agent's `io.open` fails and it dies), `lapse` sets spawn_backoff's time back, and after
every step auto-spawn's meta rows must match `backoff`, `bo`, `fails` and `halt`.

Replayed with `racy` off and no hc: a race can't be forced through the CLI, and `hc` isn't faked in the replay.
Those parts (S1's hc prompt, S2's and S4's races) are proved of the model and not replayed.

**Lifted** (board #26, rung 3): `Glob.lean` is locks.lua's lock-pattern functions line for line (a Lua string is its
bytes; fuel in place of the memo table, so `decide` runs them), and the model's `covers`, `overlap` and `refuses` are
those functions, no longer a table. Proved: `covers_iff` (covers is the pattern itself, its glob, and, for a pattern
with no `*`, `?` or `[`, everything under it as a directory), `overlaps_iff` (for byte-string patterns, overlaps is
true exactly when some path both cover; `overlaps_complete`, the half S3 uses, for any patterns) and `overlaps_comm`.
The task's other statement, "covers p q iff every path matching q matches p", is false either way round
(`covers_not_subsumed`, `covers_not_subsumes`): covers takes a path and a pattern, and `covers_iff` is what holds.
`locks_model_spec.lua` checks the Lua against Glob.lean on the 3000 committed cases and on 3000 fresh ones per
`replay.sh`: every token list, covers and overlaps agree (15,000 fresh cases at the fix); `gm` agrees with fnmatch
(flags 0) on tame patterns (`*`, `?`, plain characters, `[ab]`, `[!a]`, `[a-b]`). Elsewhere the dialect is ours, not
fnmatch's: no `[:alpha:]`, no escapes inside a class; locks.lua no longer calls fnmatch, so covers and overlaps read a
pattern alike. Before the fix (the model with `lockForms` off against the Lua before it, 9000 cases): overlaps agreed
on all but 2, where the old Lua asked fnmatch about a class fnmatch reads otherwise (`[^]`, `[]\]`); covers agreed on
every tame pattern and differed on 225 untame ones (fnmatch's escapes and brackets against the tokens').

**Lifted, the decisions** (board #27, rung 3): `Decide.lean` writes three of the Lua's decisions line for line on the
row columns they read, and proves each the model's on its view of the state. For it the Lua's inline decisions became
functions, unchanged in behaviour (the callers make the same reads, each only when the decision needs it):
`watchd.keeps(o, bg, live_addrs)`, reap's test of a lapsed claim's owner; `watchd.fate(a, t, x, has_terms, f)`,
lifecycle's verdict on a live agent (kept, `unclean`, `reuse`, `end`; `f` holds its reads as callbacks); and
`msgs.wakes(rows, cold)`, the waiter's. A read through a callback (`f.claims()`, `f.unlanded()`, `cold()`) is a `Bool` in
Lean: what it returns is the SQL's or git's (rung 4, `Env.lean`). Proved: `keeps_lifted` (on the current `Cfg`, the
row's `keeps` is the model's `keeps`), `fate_lifted` (with no hc terminals, as the replay, and `bgLives` on, the verdict is the
model's `idleFree`, `unlanded`, the background job, `reusable` in that order; `fate_end` and `fate_reuse`: `end` is `ends`, `reuse` is `reusable`),
and `wakes_lifted` (the waiter wakes exactly when `wakes`: the model has no notices, which never wake). The view: a slot's
status by its `ASt`, `aged` as idle 120 s, `big` as a context of SMALL_CTX (40k) or more, `waiter` as a live waiter pid
(`Env.waiter_alive`), a slot's hc address its number, live unless `dead`. `decide_model_spec.lua` checks the Lua against
Lean on the 3000 committed cases of each (seed 27) and on 3000 fresh ones per `replay.sh`; mutating any one of
fate's pool test, keeps' bg clause, fate's terminal-status test or wakes' urgent clause fails it.

**F1** (board #41): what `swarm state --json` reports of an idle agent (its `fate`: the verdict, the reason Home shows,
the checks the agent screen lists) is watchd's decision. The Lua does not re-derive it: state.lua runs `watchd.fate`
itself on the reads lifecycle uses (`watchd.reads`), with `f.rec`, a recorder each check calls with its value, and for
the agent screen once more with `f.all`, under which no check holds so every one is made. `fateRec` is that recorder
lifted. Proved: its verdict is `fateL` (`fateRec_verdict`), so the model's lifecycle verdict (`report_lifted`, on
`fate_lifted`'s hypotheses); every check it records is one of fate's inputs, with that input's value (`fateRec_vals`,
`Check.val`); the `f.all` run records all nine in order (`fateRec_all`); and when fate keeps the agent before the reuse
checks, the plain run's last record is the check that held, every one before it false (`fateRec_short`: Home's chip is
the reason, not a guess). `decide_model_spec.lua` checks both recorded lists on every fate case; renaming one label in
watchd.fate fails it. Not lifted: state.lua's wording of each check's detail, and its lighting of Context and Waiter
together only on a reuse verdict (display, from the same values).

What the lift found, each now a board task: reap's keep test reads the owner's terminal and the model's doesn't
(`keeps_gap`, #46): a working or prompt-blocked owner whose bound terminal hc no longer lists has its lapsed claim
reopened as a lease reap (a released message, `reaped_from` set) before the same reap ends it, where the model keeps the
claim until `reapGone` releases it with no message; `keeps_lifted` takes the case's absence as a hypothesis. The model's
one `big` bit is two thresholds in the Lua (#47): CTX_WARN (350k) for `task claim`'s fence, SMALL_CTX (40k) for
lifecycle's reuse and the cold rule, so an agent between the two (claims freely, never reused) is not modelled;
`fate_lifted` reads `big` as the second. Still to lift: `tasks.dep_path` against `reaches` (#45, a DFS with a seen set
against iterated expansion) and `conflict.owned_wts`' name matching against `owns` (#48).

The inventory, every function in `swarm/lua/swarm` by what it decides. Pure, with a counterpart in the model: locks.lua's
`tokens`, `covers`, `overlaps` (`Glob.lean`, #26); `watchd.keeps`, `watchd.fate`, `msgs.wakes` (here); `tasks.dep_path`'s
search (#45); `conflict.owned_wts` without a db (#48); `tasks.deps_of`, the `deps` column as a list (the model's
`Task.deps` is the list); `watchd.inside`, a path in a worktree (`Env.cwds_proc`). Pure, with nothing in the model to be
equal to: `msgs.capped` and `deliver`'s pick (the 9000-character budget), `fmt_msgs`, `peer_note`; `tasks.event_task`,
`task_timing`; `agents.one_line`, `hook.ctx_advice`; machine.lua's `ps_secs`, `parse_ps`, `parse_lsof`, `darwin_mem`,
`pressure_high`, `machine_line`, `claude_pid`, `proc_cmd`; conflict.lua's `edits`, `clash`, `real_hunk`, and difflib;
`cost.key`, `shell_cmd`, `median`; `run.parse_probe`; util.lua. Impure, the decision made by the SQL it runs (rung 4's
input), with the model's counterpart: `task claim`, `tasks.undone` (`select * from task where id in (..) and
state!='done'`) and the write `update task set state='claimed', .. where id=? and state='open' and not exists (select 1
from task d where d.state!='done' and ','||task.deps||',' like '%,'||d.id||',%')` (`claim`, `claimChecksDeps`), and the
fence `ctx >= CTX_WARN and not reaped_from` (`reaped_from`: the last claim or spawn event and a `reap` event; `fenced`);
`tasks.pool` (the same `not exists`, `order by title like 'main red: %' desc, id`; `pool`); `msgs.unread` and `take`
(`id>cursor and frm!=name and (dest=name or dest='@all')`, the cursor moved `where last_msg_id=from`; `unread`,
`deliverCas`); `watchd.reap` (`state='claimed' and lease_until<t`, the reopen `where id=? and owner=? and state='claimed'
and lease_until<t`; `delete from lock where path=? and agent=? and lease_until<t`; `update agent set ended=.. where
name=? and hc=? and ended is null`: `reapTask`, `reapLocks`, `reapGone`); `agents._release` (`releaseAll`); fate's reads
(`select 1 from task where owner=? and state in ('claimed','blocked')`: `holds`; `select 1 from lock where agent=?`:
`lockHeld`; the `digest` events and `unread`: `told` and passed over; `watchd.unlanded`: `unlanded`, through git);
`bases.of_agent` (`select base from task where owner=?`: `abases`) and `protected` (`select distinct base from task where
base is not null`: `pbases`); `swarm lock` (`refuses` over the held rows); `auto_spawn` (live members against meta
`agent_min`: `spawnFor`); `task after` (`dep_path` over `c:one`: `reaches`); `sweep_worktrees` (`Real.sweepGate`);
`conflict.wt_map` (agent.wt, the `workspace` rows, the branch name: `wtmap`); `agents.cold_reason` (`hc get` for a
session's last turn: the model's `cold`). The rest (ci.lua, cost.lua, run.lua, machine.lua's readers, state.lua, hook.lua's
writers, `watchd.quiet`, `hung`, `unclean`, `ensure_comms`) is outside the model (*Not modelled*).

**Lua semantics** (board #28, rung 4): `SwarmModel/Lua`, now `lua-lean/LuaLean` (lua-lean/DESIGN.md), is an executable semantics of the Lua subset `swarm/lua/swarm`
is written in: tables with `__index` classes, closures with shared upvalues (every local is a heap cell), varargs,
`pcall`/`error` (a failed call keeps what it wrote), `goto` as the continue idiom (a label ending its block; any other
goto is an error), numbers, strings as bytes, and the library the code calls: `string` (patterns, `format`, `gsub`
with string, table or function), `table` (`sort` is ltablib.c's quicksort, so ties and bad comparators come out as
LuaJIT's do), `math`, `select`, `unpack`, `pairs`, `ipairs`, `setmetatable`, `require`. Not in it: coroutines, `load`,
FFI, `__newindex` and the other metamethods, `string.format("%a")`. Effects are not interpreted: `io`, `os`, `print`, `debug`
and each module not given as source (`swarm.db`, `swarm.proc`, `posix.*`, `lfs`, `cjson`, `lua-utf8`, …) are handles,
and calling one asks an oracle (`Run.lean`: an opaque handle while modules load, nothing after). What the oracle stands
for in a real run is `Env.lean`'s `Tools`; wiring one to the other waits for a proof about a run that calls them
(board #30): the oracle sees `List Val`, and a `proc.gx` argv is a table, a heap address it can't read.

Tested the "Decoding Lua" way: `LuaCases.lean` writes random chunks (arithmetic, strings, patterns against random
subjects with every repl kind, `string.format` with random flags, widths and precisions, tables and sorts, control
flow, closures, varargs, metatables, `tonumber` on odd text) and calls of the code's own pure functions (`util.lua`,
`locks.lua`, `difflib.lua`), each with the interpreter's results; `luasem_spec.lua` runs each under LuaJIT and the
results must be the same text (numbers to the last bit, `%.17g`; table entries sorted; a top-level error only as
`error`, messages not compared, positions not being modelled). 3000 are committed, `replay.sh` checks 3000 fresh ones;
30,000 over six seeds agreed at the end. What the differences taught, now in the semantics:
LuaJIT on arm64 runs in dual-number mode, so a number is a 32-bit integer or a double, which shows only in the sign
of zero (`0 * -1` is 0, `0.5 * 0 * -1` is -0; on x86-64, doubles only, `0 * -1` is -0: lua-lean/DESIGN.md "Targets",
and a case holds both results where they differ); the parser folds arithmetic on two constants and narrows the result
to an integer, but never folds to -0 or NaN, and never negates a zero constant; `math.min`/`max` keep the running
value only when it is strictly better (so NaN and -0 land where the comparison leaves them); LuaJIT formats numbers itself
(lj_strfmt_num.c): NaN takes the space flag but not `+`, upper-case conversions write `INF`/`NAN`, and an exact tie
rounds to even except in an integer whose cut digit is 10^9 or above, which rounds up (`%.0e` of 2.5e10 is `3e+10`,
of 2.5e9 `2e+09`: nd_round's scan for a nonzero rest starts at the cut's own 9-digit limb); `%.0d` of 0 is empty;
`#t` of a table with holes is any border (Lua's rule), and the model's, the least, is not LuaJIT's, so the cases
make none. Two LuaJIT bugs are left out, not modelled: `%f` of a number below about 1e-155 overruns lj_strfmt_num.c's
64-limb buffer and prints garbage (`string.format("%.3f", 9e-160)` is `410188913345336914.062`), and the interpreter
stops on it as an unmodelled effect; and `table.unpack` does not exist in LuaJIT 2.1, so `swarm cost --top` crashes
(cost.lua:212, board #37).
Rung 4's last link (board #39), what is in and what is not. In: `LockSrc.lean`, locks.lua and util.lua as syntax trees
(`gen-lock-src.sh`, which prints them with `lua-lean dump`; `locksrc_spec.lua` in the Lua suite and `replay.sh` fail when
the file is stale), and `LuaHoare.lean` (now `lua-lean/LuaLean/Hoare.lean`), the program logic: `RunP m h P` says a computation, a function of the fuel, returns
a result and heap with `P` at every fuel from some bound on (so a total-correctness statement, stronger than "some
fuel gives ok", and it needs no partial-correctness case for small fuel: the run is what it is once the fuel suffices),
with `bind`, `succ` (the interpreter's clauses match on `n + 1`), `const` and `mono`. Not in: the proof that
locks.lua's `tokens`, `covers` and `overlaps` are Glob.lean's. What the first attempt found: the heap after
`require "swarm.locks"` is 63 objects and the kernel evaluates it (`decide +kernel` gives `H0.size = 63` and a closure's
params and environment), but a closure's body cannot be compared to the parsed source, because `Exp`/`Stat` are mutual
nested types with no `DecidableEq` (deriving refuses them) and the derived `BEq` is not kernel-reducible; the elaborator's
`rfl` times out on the load (the interpreter is well-founded recursion). So the next step is a kernel-reducible, sound
`Block` equality (hand-written structural `eqb` with `eqb = true → =`, `Num.flt` compared as unequal), then the
closure facts `H0[a]? = some (.clo ⟨ps, va, locfnBody LocksSrc name, env⟩)` by `decide +kernel`, then one `RunP`
rule per interpreter clause and per Lua function (`glob`, `startswith`, `lit`, `single`, `in_set`, `one`, `tokens`,
`meet` by induction on (#p - i) + (#q - j) with the memo invariant, `covers`, `overlaps`), the pattern lemmas for
`find("^[!^]")`, `find("]", i, true)`, `find("[*?[]")`, `gsub("/+$", "")` and `gmatch(".")`, and the bounds the task
names (#p < 32767 for i*65536+j in 32 bits; the memo key collides once #q >= 65535, under PATH_MAX 4096).

**Lifted by a translator** (board #31, rung 4): AutoCorres's first stages for our Lua. `LuaLift.lean` (now `lua-lean lift`, `lua-lean/tools/Lift.lean`) writes each
function of a file (the chunk itself is `chunk`) as three things: `f_body`, its parsed body; `f`, a shallow function in
the interpreter's monad, built from `LuaLean/Shallow.lean`'s combinators; and `f_ok`, a proof term that `f` is the
interpreter's call of the closure (since lua-lean's board #38, `D.fn_ok` applied to it: one theorem for every
program, `lua-lean/LuaLean/Denote.lean`). `CFn I (f I env0 c_x …) ⟨ps, va, f_body, env0⟩` says: for all arguments and every
fuel, `f args n = callClo I n clo args`, the same result and the same heap (`call_fn`: that is `call (n + 1) (.fn a)`
when the heap holds the closure at `a`). Its hypotheses are the closure's free names: `env0.lookup "x" = some c_x` for
an upvalue, `= none` for a global. What the shallow form drops: the syntax tree (but the bodies of the closures it
creates, which are data in the heap) and every name lookup: a local is the Lean variable naming its cell, a global is
`_G`'s field, a `goto` out of a statement is `gotos` of the block's labels. What it keeps: the fuel, threaded as each
clause threads it (`tick`), so the two are equal rather than alike; the cells, so the heap is the same heap; and
calls, which go through the interpreter's `call` (each function is lifted alone, so nothing links a call to the lifted
callee). The translator is untrusted: Lean checks each `f_ok`, so what is trusted is the parser and `Interp.lean`. A
wrong shallow function is refused: one `+` turned into `-` in a lifted function and its `f_ok` does not check. Each
proof is a term in which every lemma meets its goal by first-order unification; where a lemma's conclusion had to be
computed (`trail full`) or a projection inverted (`cx.va`), the elaborator searched for minutes, so those are side
conditions closed by `rfl`.

Results: locks.lua (20 functions, 2 s) and tasks.lua (37, 7 s) are committed (`lift.sh`; `locksrc_spec.lua` and
`replay.sh` fail when they are stale), and `chunk_body_eq` says locks.lua's chunk is #39's `LocksSrc`. Every module
under `swarm/lua/swarm`, 366 functions in 21 files, lifts and proves (`lift.sh --all`, about a minute; run.lua is the
slowest at 30 s); `replay.sh` runs it. No code/model divergence came up, and none could at this stage: the shallow
form is the interpreter, re-expressed. Rung 3's functions equal to #26's (`tokens`, `covers`, `overlaps` against
Glob.lean) is functional correctness, not translation: board #44 (RunP rules per combinator, then `glob` to `one` on
the lifted functions) and #42. The parser, checked (`lua-lean parsecheck`, in `replay.sh`): each module printed back from
its tree compiles under LuaJIT to the source's bytecode, every number constant compared at `%.17g` (the listing shows
`%.14g`); all 21 agree. A printer that re-associated `(x op y) op z` made 16 of 21 differ, so the check sees a tree's
shape. It replaces "diff the printed text against the source modulo whitespace", which the tree cannot pass: it keeps
no surface form, and the sources have 2767 `a.b`, 434 `f"s"`, 215 `function M.f`, 111 escaped strings, 45 `;`, 22
folded constants and more that print otherwise. The one thing the tree loses that bytecode sees is `else end` (an
empty else is one more `JMP`); no module has one.

Not yet, AutoCorres's later stages: locals as values (board #49: a cell no closure can write and the function writes
only at its `local` is a Lean `let`; this needs a frame theorem over the interpreter: which steps write a cell); calls
linked to lifted callees (#50: `call_fn` and the loaded heap's closure facts, #40); and a pure function lifted to a
pure Lean function without fuel or heap (#44, #42 for locks.lua).

**Environment** (board #34, rung 4c): `Env.lean` holds every assumption about the world outside the db, and `check.sh`
fails on a theorem resting on any other axiom. The model's view of the repo is `Tools.git`, under the replay's name map;
only the direction the code needs is assumed (a tool saying "landed" means landed). The twelve, each tested by the case
of its name in `env_spec.lua` (a random 24-step history of commits, squash merges and fast-forwards for the first two, run
through the Lua's own `landed_ref`, `delete_branch`, `machine.cwds`, `agents.hc_terminals`):

| Assumption | Tool | Says |
|---|---|---|
| `ancestor_reach` | `git merge-base --is-ancestor` | exit 0 is ancestry (checked against the parents the test recorded), and an ancestor's files are in the tip |
| `same_content_reach` | landed_ref's `diff --quiet` | landed_ref saying landed means the base holds the commit's files |
| `status_clean` | `git status --porcelain` | empty exactly when nothing is uncommitted, untracked and nested files included |
| `listed_on` | `git worktree list` | lists exactly the worktrees there |
| `wt_remove` | `git worktree remove` | removes a clean worktree and nothing else; refuses a dirty one and changes nothing |
| `del_ref` | `git update-ref -d refs/heads/b k` | deletes b only if its tip is k |
| `hc_ls_live` | `hc ls --json` | lists a terminal live exactly when it is |
| `hc_kill_ends` | `hc kill` | ends that terminal, no other, and leaves worktrees, branches and commits alone |
| `hc_send_targets` | `hc send` | types the line into that live terminal and no other, ends or starts no terminal, leaves worktrees, branches and commits alone |
| `kill0_alive` | `kill(p, 0)` | 0 exactly when p is in the process table |
| `cwds_proc` | `machine.cwds()` | sees a process inside a worktree exactly when the model's `proc` is set |
| `touched_recent` | mtimes, SWEEP_IDLE | the model's `recent` is the sweep's reading: touched within 1800 s |
| `now_mono` | `os.time()` | never goes back |

`Real.lean` writes each Lua decision as its lines and proves it is the model's: `sweepGate_W1` (the sweep's gate on the
tools, with no `gh` answer, is W1's premise: there, unused, no process inside, not recent, clean, HEAD reachable from a
protected ref), `landedRef_reach`, `wtRemove_only`, `delRef_guarded` (a deleted branch's tip was the HEAD the sweep
checked), `endAgent_keepsGit` (W2 at the tools: `hc kill` changes no worktree, branch or commit), `reap_gone`,
`waiter_alive` and `lapsed_stays` (a lapsed lease never reads live again, so `expire` needs no inverse). `consistent`
gives a machine with all twelve, and `real` is defined as it, so they can't prove `False`.

What the tests taught, and what the assumptions leave out: a zombie (dead, not yet reaped) answers `kill 0`, so
`kill0_alive`'s "alive" is "in the process table"; pid reuse makes a dead waiter's pid answer for another process
(the model's reading of a pid as our waiter, not an assumption here). An edit of a file below a worktree's top
directory moves neither mtime the sweep reads, though the model's `edit` sets `recent`; the edit leaves the worktree
dirty and the sweep never takes a dirty one, so no decision differs. `os.time()` is the wall clock, which NTP or a
person can step back: `now_mono` is then false and a lapsed lease reads live again. `gh`'s merged-PR answer is not
assumed (`sweepGate_W1` takes none, `landedRef_reach` passes it through): `gh pr list --head <br> --state merged`
names no base, so a PR merged into main makes landed_ref say landed on any base, `formal` too (board #43); and a PR
merged and then reverted still answers merged. `branch -d`, which `delete_branch` tries first, is not assumed
either: it checks merged into the main checkout's HEAD, and only differs from the guarded `update-ref` when the branch
moved after the sweep's check.

**Not modelled**: the red-main task and CI on the base (a PR's checks are, in `PrWatch.lean`, a layer with no leases and no time: in the main model an idle owner's lapsed claim is reaped, L2, which is how finding #30's stall ended without the fix, two hours on, the task reopened with its PR green); conflict notices and the edit hook (but for agent.wt, and the lock patterns
it matches, which are lifted); `swarm run` and machines;
of git: `origin` (the replay has none, so `main` is the base), `gh`'s merged-PR check in landed_ref (ci.pr_watch's is `gh_state`), rebases, the worktree a spawn makes
(a spawned agent's `recorded` flag and `rhead`, the base tip it was made at, stand for it: no action edits it, so it stays
clean at that HEAD, which `unlanded` checks against the agent's bases and the worktree's own (`rbase`) as the Lua does (boards #63, #78); the sweep of it once its
agent ends is not compared), an agent removing its own worktree, editing in a worktree it doesn't own or in the main checkout, merge conflicts; the unclean nudge is the action
`nudge`, not part of the tick as in the Lua: `stale` (idle 30 min) is an action that is not in `fair`, a nudge needs a
live waiter (the no-waiter notice to the communicator is a notice), and none of it is replayed (`Traces.lean` generates
`stale` only for a stayer, no `nudge`, and no `cool` for an agent its unclean worktree keeps, since 4000 s idle is past 30 min and
the Lua's tick would nudge it: PR #122's behaviour is covered by `cli_lifecycle_spec.lua`); another swarm's communicator on the board (PR #124); roles, the stay's text, `swarm spawn --stay`
and the communicator's own stay (it is no slot); of watchd.hung (board #79): the no-waiter and unwoken notices to the
communicator, and the 50 and 5 min as times (`stale` stands for both idles); watchd's quiet notice (the board empty, only
stayers live); staffing limits beyond the roster; of auto-spawn
(`Spawn.lean`): a launch failing after another spawned in the same tick (the model's `fail` is the tick's first launch),
its memory gate and the `lost` and `refused` branches (a peer's claim or spawn between the pool and the reservation),
an error that is no `exit` (it ends the tick), the human's `swarm spawn`, and launch.sh failing after hc started the
terminal while `hc ls` doesn't list it live yet (the row is undone and the agent runs anyway, with its row ended); the handoff and the fence's other half (ctx_tokens is a model bit, `big`, set when the agent stops); the background job is a flag that starts and ends (the Lua reads processes: `machine.bg_agents`), and the replay
generates none (`bgLives` is checked by `cli_lifecycle_spec`); of H1: the user as an actor apart from the communicator; of H2: `release --after` (the agent's own release has no `--after` either), the user as an
actor apart from the communicator, and the stop's text; `reaped` forgets a reap once another agent claims, so after a manual release by the retaker the Lua still lets it retake and the model does not; compaction
(`compacted_at`: the model's log only grows); death in the middle of a split command (`die` needs none pending); notices to the communicator but a block's, `swarm away`'s and `--back`'s; of the digest (board #47): merged PRs and main's CI (no PR or CI in `State`; board #80), the notes' text and the away line the hooks print to the communicator; a failed launch's row is no ended agent (the Lua's digest skips an end with no reap, leave or end event, as Sp1 says nothing is left of it); the 9000-character delivery budget
(every delivery shows all unread); `swarm join` (an ended agent never returns; its slot is a new agent); several waiters at once; the
`@all` channel; the hc terminal's own status (only its prompts are modelled, as watchd sees them).
Of the communicator (`Comms.lean`): the swarms share nothing but terminals (a worker agent's own terminal is the model's
`die`, not a `Term`); `hc ls` always answers and lists the communicator's terminal right; a launch never fails; a
session's ListAgents name is its `SWARM_NAME`, set by its last join; `swarm watchd --takeover` and a second watchd (board
#18); the human's `swarm spawn` (only watchd's spawns are placed: the starting roster is in the swarm's space). None of
it is replayed: the replay has no hc.

**Task priority (board #69)** is not modelled. The model's `pool` is an unordered filter and no theorem or replay assumes
which startable task is claimed or spawned first, so the Lua's order (the red main, then priority 0 to 3, then id) only
picks among tasks the model already allows; no statement changed. Known limit: the order is strict, there is no aging,
so P0-P2 tasks arriving one after another can starve a P3 task. L1 (`startable_taken`) holds as before because it is
about fair runs of the model, not this order; a liveness theorem about *one named* low-priority task would not hold.

## The SQL (rung 4, board #29)

`Sql.lean` gives the SQL the Lua runs a meaning, so a proof about a command (board #30) can say what each of its
statements does to the db. It is the subset the Lua uses, no more: `sql_inventory.lua` reads every db call
(`:exec`, `:one`, `:all`, `:all_cols`, `:script`) in `swarm/lua/swarm`; a call whose text is literals is its statement,
and one built from code (a column name in `agents.touch`, a `?` list, a `:format`) is a template whose statements
are listed by hand (`DYNAMIC`; the spec fails on a template without an entry). 307 sites, 262 statements: SELECT
(DISTINCT, an inner JOIN, WHERE, GROUP BY with `count(*)` and `max`, ORDER BY expressions, LIMIT, correlated `exists`
and scalar subqueries, `in` lists and subqueries; `union all` of two), INSERT (`or ignore`, `or replace`, from a SELECT, `on conflict ..
do update` with `excluded`, `returning`), UPDATE, DELETE, `create table|index if not exists`, `alter table add|drop
column`, `pragma table_info` and `journal_mode`, `begin immediate`, `commit`, `rollback`; expressions `= != < <= > >=
is [not] like [not] in || + - and or not case cast coalesce lower`.

- **Values** are NULL, INTEGER, REAL (its IEEE bits) or TEXT; no BLOB. A column's affinity comes from its declared
  type by sqlite's rules and is applied on every write (`'5'` into an `int` column is 5, 5 into a `text` one `'5'`);
  a comparison applies the affinities sqlite applies to its operands (a column's, a cast's, none); NULL is unknown in
  `= < like in and or not`, and `is` is NULL-safe. Order is NULL, numbers, text (code points, UTF-8's byte order).
- **Tables** are lists of rows with their declared columns, defaults and primary key. An `integer primary key` is the
  rowid (the next is max + 1, and with `autoincrement` past `sqlite_sequence` too, so an id is never reused); a key
  clash aborts, is ignored, replaces or updates by the statement's conflict clause; a NULL in a non-rowid key is
  allowed and clashes with nothing, as in sqlite.
- **A statement** is `exec : Conn → Stmt → List Val → Except String (Out × Conn)`: its table and column names are
  checked first, as sqlite's prepare does (`Stmt.names`); atomic (an error leaves the connection as it was), with `changes()` and `last_insert_rowid()` in the connection. A WHERE (and ON) is its
  AND-terms in order, and the row is skipped at the first that isn't true: a later term, which could fail, isn't
  evaluated (as sqlite's code does). `begin` saves the tables, `rollback` restores them, `commit` drops the copy.
  A script runs its statements in turn and stops at an error, keeping what ran.
- **A result** is column names (an alias, a column's name, else the expression's text) and rows, each in a tie group:
  rows with equal ORDER BY keys, or all rows with no ORDER BY, come out in an order sqlite doesn't define, and LIMIT may
  cut a group (`Out.cut`). The test compares a group as a multiset and a cut one by count.

**Tested**: `SqlCases.lean` builds the swarm's tables by running the inventory's own schema scripts and migrations
through `exec`, then, for each statement, random cases: 0 to 4 rows in each table it names, values by affinity from
small pools (its own literals, the same in capitals, a few others; half the time the value it compares a column with),
each `?` mostly from one random row's value of the column it is compared with (a neighbour for `<`, never for `!=`).
A migration runs on the tables without its column, the old `after` statements on a task table with one, a schema
script on no tables or all; `begin`, `commit`, `rollback` in sequences around a random write, and alone (errors).
`sql_model_spec.lua` builds the same tables in a scratch file and runs each step through db.lua (`prepare`, which
inlines integers, `all_cols`, `exec`, `script`), on a fresh connection: every step's error or success, rows, column
names, `changes()`, `last_insert_rowid()`, and after the case every table's `table_info`, rows with their storage
classes, and `sqlite_sequence` must be Lean's. 5240 committed cases and 5240 fresh per `replay.sh`, green, and about 35,000
more at other seeds while it was built. Of the committed cases' 4807 steps, 2449 return rows or change one, 46 are
errors (on both sides), and the rest are misses (a WHERE no row meets) or DDL and transaction steps. Checked to bite: with NULL sorted last, with an int written to a
`text` column as an int, or with `like` case-sensitive (this one needs about 25 cases per statement), the spec fails.

**Divergences found**: three, all gaps in the model, not bugs in the Lua, so no `Cfg` switch: sqlite (3.37 on) writes
the standard type names in capitals in `table_info` (`TEXT` for `text`; the Lua reads only `name`); a WHERE stops at
its first term that isn't true, so `delete from cmd where machine=? .. and id not in (.. limit ?)` with a NULL
`machine` doesn't fail on a text `limit`, where evaluating every term would (cost.lua passes a number there); and
sqlite resolves names when it prepares a statement, so db.connect's old `update task set deps=after where deps is
null ..` fails on a table with no `after` column even when no row has a NULL `deps` (`Stmt.names`; found by a fresh
`replay.sh` seed after the rest was green).

**Not modelled**: concurrency (one connection; *sqlite's isolation* below has it); the rowid of a table without an integer key, so
`last_insert_rowid()` after an insert into `agent`, `cursor`, `lock`, `meta`, `conflict` or `pairkey` is unknown
(the Lua reads it only after inserts into `task` and `msg`); an exponent in numeric text (`1e3`); a REAL's text beyond
whole numbers and short decimals; a compound SELECT other than one `union all` at the top (ORDER BY or LIMIT on it); a subquery in an UPDATE's SET that reads the table being updated (it would see
the table before the update; none does); ambiguous column names; an ORDER BY naming a result alias; indexes (`create
index` does nothing; an index changes only the undefined row order); the SQL's line breaks (a statement's text is
taken with each line break as a space, which changes only the name of an unaliased expression column, which no
multi-line statement has). Which row of a tie group a positional `c:one` reads is not checked against the Lua.

The kernel evaluates `exec` (`decide +kernel` in `SqlParse.lean`: `task claim`'s write refused while a dependency is
not done, taken once it is, a few seconds) and `parse` (about two minutes for that statement's text), so #30 can state
the commands' statements as `Stmt`s and their effect by evaluation. Nothing is proved about the semantics itself
yet (that a key stays unique, that `autoincrement` never reuses an id); the differential test is what ties it to
sqlite.

## sqlite's isolation (rung 4b, board #33)

Rung 4 takes each transaction as one step. `Iso.lean` says why that holds, with what sqlite documents for a WAL db and
not its internals: an engine of committed versions, one write lock, each connection's transaction and SQLITE_BUSY,
generic in the db and its statements (`Lang`; `sqlLang` is `Sql.exec`'s), and the code's choices as a `Cfg`
(`immediate`: `db:tx` begins with `begin immediate`; `migrateTx`, below). db.lua sets WAL and `busy_timeout(10000)` on
every connection; `db:tx` is `begin immediate` .. `commit`, or `rollback` when its function errors; every other
statement runs alone.

- Outside a transaction a read runs on the latest committed version; a write takes the lock (it waits for it, and gets
  SQLITE_BUSY once the busy timeout runs out, nothing changed), runs on the latest version and commits it as the next.
- `begin immediate` takes the lock, and the transaction runs on the latest version. A deferred `begin` takes nothing
  until its first statement, which reads a snapshot; a write after that gets SQLITE_BUSY at once if the lock is held, or
  if a commit came after its snapshot (BUSY_SNAPSHOT): no busy handler, and the transaction stays open.
- `commit` makes the transaction's db the next version (WAL: it never waits); `rollback` and the process ending discard
  it; both free the lock.

**Proved**, for any number of connections and any interleaving, whatever the `Cfg`: `serializable`, an invariant: each
committed version is the statements of the transaction that made it, run on the version before (`Inv.chain`), and a
transaction holding the lock began on the latest version and its db is its statements so far run on it (`Inv.writer`):
no commit comes between, so no update is lost. `stmt_out`: a statement answers on its transaction's db. So the db is
always the serial run of the committed transactions, and every answer is the one the statement gets there: a `db:tx`,
or one statement outside one, is one step, the granularity 4a assumes (a read outside a transaction is a step of its
own, which is 4a's to account for). `busyClean_of`, with `begin immediate`: SQLITE_BUSY comes only after waiting out
the timeout on another connection's lock, to a connection with no transaction open, and changes nothing, so a command
that dies of it did nothing and holds nothing. A deferred `begin` breaks it (`not_busyClean_deferred`: 0 begins and
reads, 1 commits a write, 0's write gets SQLITE_BUSY at once with its transaction open), and with `begin immediate` the
same connections wait (`immediate_waits`). The code uses `begin immediate`, so that switch is no Lua bug.

**Assumed** (`Env.lean`, five axioms): real sqlite is this engine, one assumption per kind of op (`sqlite_begin`,
`sqlite_read`, `sqlite_write`, `sqlite_commit`, `sqlite_rollback`): `Db.Does w c op r w'`, connection c asking op and
getting r, is an engine step from `view w` to `view w'`, a run being a sequence of such ops (sqlite orders access to the
file and the WAL index with locks, and a statement's rows come from the snapshot its first step took).
`sqlite_consistent`: the engine has them all. `Real.lean`: `realDb_reach` (a run of the real db is a run of the
engine), so `real_serializable`, `real_stmt_out` and `real_busyClean`. Each is stress-tested against real sqlite through
db.lua by `sqlite_spec.lua`, in about 3 s: 6 processes each 150 times read a counter, write it + 1 and log the value
read in `db:tx`, and add 1 to another outside a transaction; 3 move 1 between random accounts in `db:tx`; 3 read the
total. No process fails (each waits within the busy timeout), no update to either counter is lost, each value is read
once (every transaction read the latest), and no read sees half a transfer. Against a holder of the lock, a connection
with a 0.2 s busy timeout: `begin immediate` and a write outside a transaction wait 0.2 s and fail, nothing changed and
no transaction left open; its reads don't wait and don't see the holder's write; a commit doesn't wait for a reader
that holds a snapshot. The deferred counterexample on real sqlite: SQLITE_BUSY at once, the transaction still open. A
process SIGKILLed in a transaction, and a `db:tx` whose function errors: nothing of it left, the lock free,
`integrity_check` ok. Checked to bite: without `db:tx` around the counters and transfers, readers see half a transfer
and the counter loses updates.

**Findings**, both in db.connect, both Lua bugs, both fixed:

1. The column migration (`db.COLUMNS`) read the columns, then added each missing one, every statement on its own.
   Two connects at once of a db missing a column both read it missing and both add it; the second dies of "duplicate
   column name". Every fresh db goes through it (the schema script makes the tables without the later columns), so a
   swarm's first commands at once crashed. Eight connects at once failed 29 times in 160 on an old db, and at least 73
   in 240 on fresh ones. The model: `MReach` runs any number of connects on the engine; with `migrateTx` on they read
   the columns and, when one is missing, take `begin immediate`, read them again and add those still missing:
   `migrate_ok`, no connect fails but of SQLITE_BUSY. With it off (the Lua before), `not_migrate_ok`: two connects,
   one column. The fix is the same in db.lua (a db with every column takes no lock). `db_spec.lua` runs 12 rounds of 8
   connects at once on fresh and old dbs; it fails on the old db.lua.
2. Found by that test once the first was fixed: on a fresh db, `pragma journal_mode=wal` (the switch to WAL) gets
   SQLITE_BUSY at once while another first connect switches it; sqlite calls no busy handler for it. Not in the model,
   whose db is WAL from the start. Fix: db.connect tries it again every 20 ms, up to 10 s, on "database is locked".

**Not modelled**: the rollback journal: the cmd-cost history (`db.open_at`) isn't WAL, so there a reader holds up a
commit and a commit can get SQLITE_BUSY with its transaction left open, which `db:tx` would not roll back (cost.lua runs
no transaction on it); the busy timeout as time (a wait is a step not taken, and SQLITE_BUSY may end any wait); IO
errors; `changes()` and `last_insert_rowid()`, which are the connection's; the switch to WAL.

## Using these proofs downstream

A proof about a program that uses the swarm (a client of its CLI, a tool that reads its db) can import
`SwarmModel.Contract` and build on what is proved instead of guessing. Add this package to your lakefile (`[[require]]`
`name = "swarm-model"`, `path = ".../swarm/model"`, or a git source with `subDir = "swarm/model"`), then `import
SwarmModel.Contract`. `example/Client.lean` is a worked consumer: a toy client that works only on a task it believes it
claimed, proved never to work on a task another agent holds (`never_works_on_others`, from `s1_believes_held`), and
`env_landedRef` used on `Env.ideal` with its two assumptions proved in place.

What is proved. `Contract.lean` lists the theorems, each with what it guarantees and what it rests on: S1-S5 of every
reachable state (`s1_oneWorker`, `s1_believes_held`, `s2_noEarlyStart`, `s3_noSharedFile`, `s4_inboxExact`,
`s5_doneHasEvidence`), W1 and N1 of every step and tick (`w1_gcOk`, `n1_noWorkLost`), L2 and L4 over fair runs
(`l2_idleClaim`, `l4_deadLive`), N1' of a nudge (`n1'_nudge`), and at the tools: `env_landedRef`, `env_sweepGate`, `env_reapGone`, `db_serializable`.
The model theorems hold for every `Cfg` whose switches they take as hypotheses (the fixes; main runs with them on) and
rest on Lean's axioms alone. They are about the model: that the Lua does what the model does is replayed (random and
scripted runs through the CLI, `cli_model_spec.lua`), and proved only for what is lifted (`Lifted/`, `Decide.lean`,
`Real.lean`); *What is proved, what is replayed, what isn't modelled* says which.

What is assumed. The tool theorems take `Env.lean`'s assumptions as hypotheses on any `Tools` or `Db`, so a
downstream proof chooses: supply them for a machine of its own (`Env.consistent` proves them all for `Env.ideal`,
`Env.sqlite_consistent` for `Env.idealDb`), or use the `real` versions in `Real.lean` (`Env.landedRef_reach`,
`Env.realDb_sound`, …), which rest on the 21 axioms of `Env.lean` about the machine the swarm runs on, each a claim
about git, hc, gh, the kernel, the clock or sqlite that a test checks, not a proof.

How to recheck. `swarm/model/check.sh` builds every theorem (`lake build`), runs `Audit.lean`, which prints each
theorem resting on an environment assumption with the ones it uses and fails on any other axiom (no `sorry`, no
`native_decide`), and checks `example/Client.lean`. Each assumption's test is the case named after it:
`luajit swarm/lua/test/run.lua env` runs `env_spec.lua` (git, the kernel, files, the clock; `SWARM_TEST_HC=1` adds
`hc_ls_live`, `hc_run_starts`, `hc_send_targets` and `hc_kill_ends`, which start terminals in your hc; `SWARM_TEST_GH=1` adds `gh_checks` and `gh_state`,
which ask GitHub about this repo's PRs), and `luajit swarm/lua/test/run.lua sqlite` runs `sqlite_spec.lua` (the five
sqlite ones, many processes at once).

## Running

```sh
swarm/model/check.sh            # every theorem and counterexample, about 12 s
swarm/model/replay.sh 60 40     # 60 fresh 40-step runs through the CLI, and fresh glob, Lua and SQL cases
luajit swarm/lua/test/run.lua sql_model   # the committed SQL cases
# after a change to a statement or the schema, regenerate the SQL cases:
luajit swarm/lua/test/sql_inventory.lua > /tmp/inv &&
  (cd swarm/model && lake env lean --run SwarmModel/SqlCases.lean /tmp/inv 20 29 /tmp/sql.json) &&
  gzip -9c /tmp/sql.json > swarm/model/sqlcases.json.gz
luajit swarm/lua/test/run.lua cli_model   # the committed runs (also part of the whole suite)
luajit swarm/lua/test/run.lua luasem      # the committed Lua chunks under LuaJIT
swarm/model/lift.sh                       # after a change to locks.lua, tasks.lua or watchd.lua: regenerate Lifted/
swarm/model/lift.sh --all                 # every module lifted and proved, in a scratch directory
lua-lean/check.sh                         # lua-lean on its own
lua-lean/lua-lean parsecheck swarm/lua/swarm/*.lua   # the parser against LuaJIT's bytecode
SWARM_TEST_HC=1 luajit swarm/lua/test/run.lua env   # Env.lean's assumptions against git, hc, the kernel, the clock
luajit swarm/lua/test/run.lua sqlite      # and its sqlite assumptions against sqlite, many processes at once
lua-lean/lua-lean run --lib swarm=swarm/lua/swarm f.lua   # f.lua under the Lean semantics, and
LUA_PATH='swarm/lua/?.lua;;' luajit lua-lean/test/luasem.lua f.lua   # under LuaJIT, written alike
```

`check.sh` and `replay.sh` need `lake` (elan) on the PATH, or nix, which they use to fetch it
(`nix shell nixpkgs#elan`). The Lua suite needs neither.

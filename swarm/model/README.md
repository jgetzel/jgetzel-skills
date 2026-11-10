# A Lean model of the swarm's coordination

`SwarmModel/Model.lean` models what `swarm/lua/swarm` does to coordinate agents: the board (tasks and their
`--after` dependencies), leases and watchd's reaping and auto-spawn, locks, agents, and inboxes. It is plain
Lean 4: one `State`, and one function per command or event. [Veil](https://github.com/verse-lab/veil) checks
it exhaustively on small bounds (`check.sh`). Random runs of it are replayed through the real CLI against a
scratch `swarm.db` (`replay.sh`, and the committed `traces/` in the Lua suite), so a model that drifts from the
code fails a test.

It replaces the Quint model of board task #107 (branch `sr-92/quint-model`, never merged), whose TLC checks were
too slow: *Results* compares the two.

| File | What it is |
|---|---|
| `SwarmModel/Model.lean` | the model: state, actions, the properties below as functions, and the instances |
| `SwarmModel/Checks.lean` | the model as a Veil transition system, and every check with the verdict wanted |
| `SwarmModel/Expect.lean` | `#expect`: runs one check and compares its verdict |
| `SwarmModel/Traces.lean` | writes random runs of the `replay` instance as JSON |
| `check.sh [name]` | runs every check (or those whose name has `name`); exits 1 if a verdict differs |
| `replay.sh [n] [steps] [seed]` | `n` fresh runs, each replayed through the CLI |
| `traces/*.json.gz` | 12 runs of 50 steps (seed 107) the Lua suite replays |
| `../lua/test/cli_model_spec.lua` | the replay: one test per trace |
| `lakefile.toml`, `lean-toolchain`, `lake-manifest.json` | Lean 4.35.0 and Veil's `v4.35.0` tag, every dependency pinned by commit |

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
  Stop hook's `swarm wait`), small or big context, cold or not (idle past the prompt cache with a big context).
  An agent's slot is reused by the next spawn after it ends (the Lua gives that agent the next name; the replay
  maps slots to names).
- **Messages** are one log with a cursor per agent. A hook, `swarm read`, a wake, a boot and the end of an hc
  prompt deliver every unread message. The waiter wakes the agent on an urgent message, or on any message if
  the agent isn't cold.
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
| `"emptyEvidence"` in `off` | `done --evidence ""` is accepted | PR #113 refuses it |
| `lockOverlap` | `lock` refuses only a pattern covering the other | PR #114 refuses any common file |
| `deliverCas` | a delivery's cursor write ignores a delivery in between | PR #115 writes only from where it read |
| `passedOver` | a reusable agent holds spawn back forever | PR #116 ends one that passed the work over |
| `waiterAlive` | an idle agent whose waiter exited is kept reusable, and never reads its digest | PR #119 ends it |

`racy` splits two commands into the read and the write the Lua does separately: `task claim` (the dependency
check, then the update) and the waiter's delivery (unread, then the cursor). `off` turns off parts of the
environment an instance doesn't need, so a check can exhaust it. `compact` drops messages whose reader has
passed them, so inboxes stay finite.

Instances: `sim_before` (624cf79), `sim_first106` (b04cf08) and `sim_after` (main now) have every feature on,
for random runs; `replay` is `sim_after` without hc or races, what the replay drives. The `s*_` and `l*_`
instances are what Veil exhausts: 2 agent slots, 1 to 3 tasks.

## Properties

Each is a sentence, then its name in `Model.lean` (safety) or `Checks.lean` (liveness).

Safety:

- **S1** No task has two agents at work on it: no two agents, each working or at an hc prompt, both believe they
  hold the same task. `oneWorker`
- **S2** No task is claimed while a task it is after isn't done. `noEarlyStart`
- **S3** No two live locks of different agents cover a common file. `locksDisjoint`
- **S4** No message is shown twice, and no cursor passes a message it didn't show. `inboxExact`
- **S5** Every done task has evidence. `doneHasEvidence`

Liveness, under fairness (watchd ticks; leases lapse and idle agents age; a waiter with a message it wakes on
wakes; a spawned agent boots; a working agent reads its messages and takes work it is repeatedly able to):

- **L1** A startable task doesn't stay startable forever while a slot is free. `L1`
- **L2** A claimed task whose owner is idle is eventually done or open again, unless its owner gets back to
  work. `L2`
- **L3** An unblock answer eventually reaches whoever holds the task, unless the task ends. `L3`

## Results

RESULTS

## Findings

Every counterexample the Quint model found, and what fixed it. `check.sh` shows each one again in the Lean
model: the bug with the fix's switch off, no violation with it on (`TRACES=1 check.sh <name>` prints the
run). Each was a real execution of the Lua.

| # | Property | Check that fails / holds | The counterexample | Fixed by |
|---|---|---|---|---|
| 1 | L2 | `l_before` / `l_first106`, `l_after` | An owner goes idle holding a claim and nothing wakes it; its lease lapses, but reap keeps a lapsed claim while the owner is live, so the task stays claimed forever (task #106, seen live for ~6 h). | b04cf08, PR #110 |
| 2 | S1 | `s1_first106` / `s1_after` | #1's first fix reopens a lapsed claim whenever the owner isn't working, including one stuck at an hc permission prompt; another agent claims it, the prompt is answered, and two agents work on the task. | edffafc, PR #111 |
| 3 | L3 | `l_before` / `l_fixed` | An unblock answer is only a DM. An idle owner that is cold isn't woken by a non-urgent message, so the answer never reaches it, and no one else can read it. | b04cf08, PR #110 (`answerOnTask`) |
| 4 | S2 | `s2_racy` / `s2_fixed` | `task claim` checks the dependencies, then a `task after` adds one that isn't done, then the claim's write (`where state='open'`) succeeds: a task starts before what it is after. | 58e9aa6, PR #112 |
| 5 | S5 | `s4_atomic` / `s5_fixed` | `task done --evidence ""` is accepted. | 89fe2a2, PR #113 |
| 6 | S3 | `s3_globs` / `s3_fixed` | `m/a*` and `m/*.lua` both match `m/a.lua`, but neither covers the other as a path, so both locks are granted. | cc63217, PR #114 |
| 7 | S4 | `s4_racy` / `s4_fixed` | The waiter reads the unread list, a hook delivers it and moves the cursor, the waiter writes its cursor and shows the same message again. | 5cdcb42, PR #115 |
| 8 | L1, L3 | `l_after` / `l_fixed` | A small-context idle agent is reusable while work is open; it reads the digest and stops without taking the task (it may), and lifecycle keeps it reusable, so it spawns no one for a startable task with a free slot. | 1ac83b1, PR #116 |
| 9 | L1, L3 | `l_fixed_waiter` / `l_waiter` | The same with a waiter that timed out (21000 s): the agent never reads the digest, so it stays reusable and holds spawn back; an answer to it goes unread. | aeaf44f, PR #119 (board #113) |

Still failing, by design: in `l_after_waiter`, the same model as #9 with PR #116's rule off, L1 and L3 fail for
both reasons. Nothing is open: every counterexample above has a fix on main.

## What is checked, what is replayed, what isn't modelled

**Checked** (Veil, exhaustive within the bounds): the verdicts above, for 2 agent slots (a roster of 2, refilled
as agents end), 1 to 3 tasks, the locks and message counts each instance sets, and the parts of the environment
it leaves on. A property that holds is checked for those bounds only; the counterexamples are real executions
of the model at any size. Nothing is proved for every size yet: board task #112 does that for S1 to S5.
`#temporal_check`'s verdicts are proved correct in Lean by Veil; `#model_check`'s search is not.

**Replayed** (random, not exhaustive): that the model is the code. Each step of a run does the command it stands
for (`task claim`, `lock`, `post`, `hook stop`, `swarm wait`, `watchd --once`, …) or, for time and the world,
writes the db (`lease_until` in the past, `last_active` back 200 s or 4000 s, `ctx_tokens`, the waiter's pid:
the test's own while the model's waiter is alive, none once it is gone), and then the db must match the model:
every task's state, owner, live lease, evidence and answer; every agent's status; every lock; every message to
an agent, in order; and each agent's unread list. The 12 committed runs (seed 107, 50 steps) are in the Lua
suite; `replay.sh 60 40` does 60 fresh ones in about 2 minutes. REPLAY

Replayed with `racy` off and no hc: a race can't be forced through the CLI, and `hc` isn't faked in the replay.
Those parts (S1's hc prompt, S2's and S4's races) are checked in the model only.

**Not modelled**: the red-main task and CI; conflict notices and the edit hook; `swarm run` and machines;
worktrees and `landed` (every agent's work counts as landed), so neither PR #122's nudge to an agent kept only
by an unclean worktree nor PR #123's every-worktree rule (board #119); a background job keeping an idle owner's
claim (PR #121, board #118); another swarm's communicator on the board (PR #124); roles and `swarm stay`
(no model agent stays, so lifecycle may end any of them); staffing limits beyond the roster; auto-spawn's
launch failures, backoff and halt; the context fence on `task claim` (350k) and the handoff; compaction
(`compacted_at`); notices to the communicator; the 9000-character delivery budget (every delivery shows all
unread); `swarm join` (an ended agent never returns; its slot is a new agent); several waiters at once; the
`@all` channel; the hc terminal's own status (only its prompts are modelled, as watchd sees them).

## Running

```sh
swarm/model/check.sh            # every check; or check.sh s1_ for one group; TRACES=1 prints counterexamples
swarm/model/replay.sh 60 40     # 60 fresh 40-step runs through the CLI
luajit swarm/lua/test/run.lua cli_model   # the committed runs (also part of the whole suite)
```

`check.sh` and `replay.sh` need `lake` (elan) and `unzip` on the PATH, or nix, which they use to fetch both
(`nix shell nixpkgs#elan nixpkgs#unzip`); the liveness checks also need a C compiler. The first run downloads
and builds Veil and its dependencies into `.lake/` (about 20 minutes, 3 GB). The Lua suite needs none of it.

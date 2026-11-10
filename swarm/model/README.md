# A Quint model of the swarm's coordination

`swarm.qnt` models what `swarm/lua/swarm` does to coordinate agents: the board (tasks and their
`--after` dependencies), leases and watchd's reaping and auto-spawn, locks, agents, and inboxes.
TLC checks it exhaustively on small bounds (`check.sh`). Random traces of it are replayed through the
real CLI against a scratch `swarm.db` (`replay.sh`, and the committed `traces/` in the Lua suite), so a
model that drifts from the code fails a test.

| File | What it is |
|---|---|
| `swarm.qnt` | the spec: state, actions, the properties below, and the instances checked |
| `check.sh` | runs TLC on each (instance, property) and compares the verdict with the table below |
| `replay.sh [n] [steps] [seed]` | `n` fresh traces of the `replay` instance, each replayed through the CLI |
| `traces/*.itf.json.gz` | 12 traces of 50 steps (seed 107) the Lua suite replays |
| `../lua/test/cli_model_spec.lua` | the replay: one test per trace |

## The model

One variable `s` holds the whole state; every watchd tick is a pure function of it, composed as the
Lua composes it (`reap` tasks, `reap` locks, `lifecycle`).

- **Tasks** are absent, open, claimed, blocked, done or dropped, with an owner, `--after`
  dependencies, a lease (live or lapsed), evidence (empty or not), and the unblock answer if any.
  Agents claim, renew, release, block, finish (`done --evidence`) and drop their own; the communicator
  adds (`--after`), changes dependencies (`task after`, cycles refused), unblocks with an answer, and
  drops any task.
- **Leases** lapse as time passes (`expire`). Reap reopens a lapsed claim by the rule of the release
  being modelled (`RELEASE`, below) and tells the owner.
- **watchd's lifecycle**: an idle agent past 2 minutes with no claim or lock is ended, unless its
  context is small and the pool has work: then it is *reusable*, and gets a digest message once per new
  pool id. With no reusable agent, watchd spawns into free slots (up to the roster), one per startable
  task, and the new agent's first turn reads its task.
- **Locks** are patterns; `swarm lock` refuses a pattern that covers, or is covered by, a live lock of
  another agent (`locks.covers`, tabulated for the model's patterns). Locks lapse and are reaped.
- **Agents** are working, idle, blocked (an hc permission prompt) or ended, with or without a live
  waiter (the Stop hook's `swarm wait`), small or big context, cold or not (idle past the prompt
  cache with a big context). An agent's slot is reused by the next spawn after it ends (the Lua gives
  that agent the next name; the replay maps slots to names).
- **Messages** are one log with a cursor per agent. A hook, `swarm read`, a wake, a boot and the end of
  an hc prompt deliver every unread message. The waiter wakes the agent on an urgent message, or on any
  message if the agent isn't cold.
- `believes` (the tasks an agent thinks it holds), `seen` (what each agent was shown), `pend` (answers
  not yet read by the task's holder) and `early` are ghosts: they exist for the properties.

The agents' choices are free (any command, in any order) with one assumption from the brief: an agent
with a small context, no claim and work in the pool takes work before it stops.

Agents run a command only with an empty inbox: the PreToolUse hook delivers before every one.

Each fix the model found or confirmed is a switch, so the spec records the code before and after it:

| Switch | Before | After |
|---|---|---|
| `RELEASE` | `ended`: 624cf79 keeps a lapsed claim while its owner is live | `notWorking`: b04cf08 (PR #110) reopens it unless the owner is working; `idle`: edffafc (PR #111) only when the owner is idle |
| `ANSWER_ON_TASK` | the unblock answer is only a DM | PR #110 stores it on the task |
| `CLAIM_CHECKS_DEPS` | `task claim`'s write checks only `state='open'` | PR #112 checks the dependencies in the write |
| `"emptyEvidence"` in `OFF` | `done --evidence ""` is accepted | PR #113 refuses it |
| `LOCK_OVERLAP` | `lock` refuses only a pattern covering the other | PR #114 refuses any common file |
| `DELIVER_CAS` | a delivery's cursor write ignores a delivery in between | PR #115 writes only from where it read |
| `PASSED_OVER` | a reusable agent holds spawn back forever | PR #116 ends one that passed the work over |
| `WAITER_ALIVE` | an idle agent whose waiter exited is kept reusable, and never reads its digest | PR #119 ends it |

`RACY` splits two commands into the read and the write the Lua does separately: `task claim` (the
dependency check, then the update) and the waiter's delivery (unread, then the cursor). `OFF` turns off
parts of the environment an instance doesn't need, so TLC can exhaust it. `COMPACT` drops messages
whose reader has passed them, so inboxes stay finite.

Instances: `before` (624cf79), `first106` (b04cf08) and `after` (main now) have every feature on, for
the simulator; `replay` is `after` without hc, what the replay drives; `quint run --main after --invariant safety` finds nothing in 2000 random 30-step runs,
and `--main before` fails at once. The `s*_` and `l*_` instances are what TLC exhausts.

## Properties

Each is a sentence, then its name in `swarm.qnt`.

Safety:

- **S1** No task has two agents at work on it: no two agents, each working or at an hc prompt, both
  believe they hold the same task. `oneWorker`
- **S2** No task is claimed while a task it is after isn't done. `noEarlyStart`
- **S3** No two live locks of different agents cover a common file. `locksDisjoint`
- **S4** No message is shown twice, and no cursor passes a message it didn't show. `inboxExact`
- **S5** Every done task has evidence. `doneHasEvidence`

Liveness, under fairness (watchd ticks; leases lapse and idle agents age; a waiter with a message it
wakes on wakes; a spawned agent boots; a working agent reads its messages, finishes a two-step write,
and takes work it is repeatedly able to; an hc prompt is answered):

- **L1** A startable task doesn't stay startable forever while a slot is free. `L1`
- **L2** A claimed task whose owner is idle is eventually done or open again, unless its owner gets back
  to work. `L2`
- **L3** An unblock answer eventually reaches whoever holds the task, unless the task ends. `L3`

## Results

`check.sh`: TLC, 2 agent slots, 1 task for S1 and liveness, 1–3 for the rest. Times are from one run on a
24-core machine. A check that hit the cap (20 or 30 minutes) is *not proved at this bound*.

| Instance | Property | Verdict | States | Time |
|---|---|---|---|---|
RESULTS

## Findings

Every counterexample TLC found, and what fixed it. Each was a real execution of the Lua (the replay
shows the model is the code), and each fix is a switch above, so `check.sh` shows the bug, then the fix.

| # | Property | Instance | The counterexample | Fixed by |
|---|---|---|---|---|
| 1 | L2 | `l_before` | An owner goes idle holding a claim and nothing wakes it; its lease lapses, but reap keeps a lapsed claim while the owner is live, so the task stays claimed forever (task #106, seen live for ~6 h). | b04cf08, PR #110 |
| 2 | S1 | `s1_first106` | #1's first fix reopens a lapsed claim whenever the owner isn't working, including one stuck at an hc permission prompt; a spawned agent claims it, the prompt is answered, and two agents work on the task. | edffafc, PR #111 |
| 3 | L3 | `l_before` | An unblock answer is only a DM. An idle owner that is cold isn't woken by a non-urgent message, so the answer never reaches it, and no one else can read it. | b04cf08, PR #110 (`ANSWER_ON_TASK`) |
| 4 | S2 | `s2_racy` | `task claim` checks the dependencies, then a `task after` adds one that isn't done, then the claim's write (`where state='open'`) succeeds: a task starts before what it is after. | 58e9aa6, PR #112 |
| 5 | S5 | `s4_atomic` | `task done --evidence ""` is accepted. | 89fe2a2, PR #113 |
| 6 | S3 | `s3_globs` | `m/a*` and `m/*.lua` both match `m/a.lua`, but neither covers the other as a path, so both locks are granted. | cc63217, PR #114 |
| 7 | S4 | `s4_racy` | The waiter reads the unread list, a hook delivers it and moves the cursor, the waiter writes its cursor and shows the same message again. | 5cdcb42, PR #115 |
| 8 | L1, L3 | `l_after` | A small-context idle agent is reusable while work is open; it reads the digest and stops without taking the task (it may), and lifecycle keeps it reusable, so it spawns no one for a startable task with a free slot. | 1ac83b1, PR #116 |
| 9 | L1, L3 | `l_fixed_waiter` | The same with a waiter that timed out (21000 s): the agent never reads the digest, so it stays reusable and holds spawn back; an answer to it goes unread. | aeaf44f, PR #119 (board #113) |

Still failing, by design: in `l_after_waiter`, the same model as #9 with PR #116's rule off, L1 and L3 fail
for both reasons. Nothing is open: every counterexample above has a fix on main. The model doesn't yet
cover PRs #121–#124 (see *Not modelled*); board tasks #118 and #119 add them.

## What is proved, what is replayed, what isn't modelled

**Proved** (TLC, exhaustive within the bounds): the verdicts above, for 2 agent slots (a roster of 2,
refilled as agents end), 1–3 tasks, the locks and message counts each instance sets, and the parts of
the environment it leaves on. A property that holds is proved for those bounds only; the counterexamples
are real executions of the model at any size.

**Replayed** (random, not exhaustive): that the model is the code. Each step of a trace runs the command
it stands for (`task claim`, `lock`, `post`, `hook stop`, `swarm wait`, `watchd --once`, …) or, for time
and the world, writes the db (`lease_until` in the past, `last_active` back 200 s or 4000 s,
`ctx_tokens`, the waiter's pid: the test's own while the model's waiter is alive, none once it is gone),
and then the db must match the model: every task's state, owner, live lease, evidence and
answer; every agent's status; every lock; every message to an agent, in order; and each agent's unread
list. The 12 committed traces (seed 107, 50 steps) run in the Lua suite, about 30 s of its ~50 s;
`replay.sh 60 40` runs 60 fresh ones in about 2.5 minutes (seeds 124, 1192 and 2026 passed). The replay
catches drift: before this model gained `WAITER_ALIVE`, PR #119 failed 2 of the 12 committed traces, and a
mutant `replay` with `WAITER_ALIVE = false` fails 3 of 40 fresh traces. It is weaker where a divergence
needs a rare sequence: a mutant with 624cf79's reap rule fails 1 of 40 50-step traces (seed 107), and 0 of
40 40-step ones (seed 106).

Replayed with `RACY` off and no hc: a race can't be forced through the CLI, and `hc` isn't faked in
the replay. Those parts (S1's hc prompt, S2's and S4's races) are checked in the model only.

**Not modelled**: the red-main task and CI; conflict notices and the edit hook; `swarm run` and machines;
worktrees and `landed` (every agent's work counts as landed), so neither PR #122's nudge to an agent kept only
by an unclean worktree nor PR #123's every-worktree rule; a background job keeping an idle owner's claim
(PR #121: the replay's agents have no claude process, so none has one); another swarm's communicator on
the board (PR #124); auto-spawn's launch failures, backoff and
halt; the context fence on `task claim` (350k) and the handoff; compaction (`compacted_at`); notices to
the communicator; the 9000-character delivery budget (every delivery shows all unread); `swarm join`
(an ended agent never returns; its slot is a new agent); several waiters at once; the `@all` channel;
the hc terminal's own status (only its prompts are modelled, as watchd sees them).

## Running

```sh
swarm/model/check.sh            # all TLC checks; or check.sh s1_ for one group
swarm/model/replay.sh 60 40     # 60 fresh 40-step traces through the CLI
luajit swarm/lua/test/run.lua cli_model   # the committed traces (also part of the whole suite)
nix shell nixpkgs#quint -c quint run --main after --invariant safety --max-steps 30 swarm/model/swarm.qnt
```

`check.sh` and `replay.sh` need nix (quint 0.33 and a JDK from nixpkgs). The suite needs neither.

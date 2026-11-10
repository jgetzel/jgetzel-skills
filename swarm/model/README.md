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

`RELEASE` picks the reap rule: `ended` is 624cf79 (before #106: a lapsed claim is kept while its owner
is live), `notWorking` is b04cf08 (reopened unless the owner is working), `idle` is edffafc, the code
now (reopened only when the owner is idle). `RACY` splits two commands into the read and the write the
Lua does separately: `task claim` (dependency check, then `update … where state='open'`) and the
waiter's delivery (unread, then the cursor). `OFF` turns off parts of the environment an instance
doesn't need, so TLC can exhaust it; `COMPACT` drops messages every reader has passed, so inboxes stay
finite.

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

`check.sh` (TLC 2 agent slots, 1–3 tasks; a few seconds to minutes each, times below from one run):

| Instance | Property | Verdict | States | Time |
|---|---|---|---|---|
RESULTS

## Findings

FINDINGS

## What is proved, what is replayed, what isn't modelled

**Proved** (TLC, exhaustive within the bounds): the verdicts above, for 2 agent slots (a roster of 2,
refilled as agents end), 1–3 tasks, the locks and message counts each instance sets, and the parts of
the environment it leaves on. A property that holds is proved for those bounds only; the counterexamples
are real executions of the model at any size.

**Replayed** (random, not exhaustive): that the model is the code. Each step of a trace runs the command
it stands for (`task claim`, `lock`, `post`, `hook stop`, `swarm wait`, `watchd --once`, …) or, for time
and the world, writes the db (`lease_until` in the past, `last_active` back 200 s or 4000 s,
`ctx_tokens`), and then the db must match the model: every task's state, owner, live lease, evidence and
answer; every agent's status; every lock; every message to an agent, in order; and each agent's unread
list. The 12 committed traces run in the Lua suite (about 15 s); `replay.sh 60 40` runs 60 fresh ones in
about a minute. A mutant model with 624cf79's reap rule fails 4 of 40 traces against the current code.

Replayed with `RACY` off and no hc: a race can't be forced through the CLI, and `hc` isn't faked in
the replay. Those parts (S1's hc prompt, S2's and S4's races) are checked in the model only.

**Not modelled**: the red-main task and CI; conflict notices and the edit hook; `swarm run` and machines;
worktrees and `landed` (every agent's work counts as landed); auto-spawn's launch failures, backoff and
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

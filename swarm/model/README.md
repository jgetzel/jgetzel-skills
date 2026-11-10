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
| `SwarmModel/Locks.lean` | S3 |
| `SwarmModel/Inbox.lean` | S4, and `tick_inv`: a property every part of watchd's tick keeps is kept by the tick |
| `SwarmModel/Workers.lean` | S1 |
| `SwarmModel/Findings.lean` | the thirteen counterexamples as runs, and the same runs with the fix on |
| `SwarmModel/Liveness.lean` | the parts of L2 and L4 that are proved |
| `SwarmModel/Fair.lean` | fair runs (`Run`, `Run.Fair`) and L2 over them: `idleClaim_leads_to` |
| `SwarmModel/Traces.lean` | writes random runs of the `replay` instance as JSON |
| `check.sh` | builds the model, which checks every theorem and run; fails on `sorry`, `native_decide` or an axiom |
| `replay.sh [n] [steps] [seed]` | `n` fresh runs, each replayed through the CLI |
| `traces/*.json.gz` | 12 runs of 50 steps (seed 107) the Lua suite replays |
| `../lua/test/cli_model_spec.lua` | the replay: one test per trace |
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
  Stop hook's `swarm wait`), small or big context, cold or not (idle past the prompt cache with a big context).
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
| `deliverCas` | a delivery's cursor write ignores a delivery in between | PR #115 writes only from where it read |
| `passedOver` | a reusable agent holds spawn back forever | PR #116 ends one that passed the work over |
| `waiterAlive` | an idle agent whose waiter exited is kept reusable, and never reads its digest | PR #119 ends it |
| `bgKeeps` | reap reopens a lapsed claim of an idle owner even while its background job runs | PR #121 keeps it |
| `retake` | the 350k fence on `task claim` refuses a task reap took from that very agent | PR #121 lets it retake (`reaped`, the Lua's `reaped_from`) |
| `allWts` | lifecycle keeps an agent only for the one worktree `wt_map` picks | PR #123 keeps it while any worktree it owns is unlanded |
| `uncleanNudge` | an idle agent kept only by an unclean worktree is kept silently, forever | PR #122 sends one urgent nudge per idle stretch |

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
  hold the same task. `oneWorker`
- **S2** No task is claimed while a task it is after isn't done. `noEarlyStart`
- **S3** No two live locks of different agents cover a common file. `locksDisjoint`
- **S4** No message is shown twice, and no cursor passes a message it didn't show. `inboxExact`
- **S5** Every done task has evidence. `doneHasEvidence`

Liveness, under fairness (the actions of `fair` in `Findings.lean`: watchd ticks; leases lapse and idle agents
age; a waiter with a message it wakes on wakes; a spawned agent boots; an hc prompt is answered; a working agent
reads its messages and takes work):

- **L1** A startable task doesn't stay startable forever while a slot is free. Its negation in one state:
  `idleSlot`
- **L2** A claimed task whose owner is idle is eventually done or open again, unless its owner gets back to
  work. `idleClaim`
- **L3** An unblock answer eventually reaches whoever holds the task, unless the task ends. `answered`
- **L4** A row whose terminal is gone is eventually ended (its claims and locks released). Its negation in one state:
  `deadLive`. Fairness: watchd ticks, and an `hc ls` that lists the terminal as gone. `watchd := false` (no watchd), a
  failing `hc ls`, and an unbound row each break it (findings #14, #15)

## Results

`check.sh` (`lake build`) checks everything below in about 12 seconds from nothing (16 s of CPU). No `sorry`,
no `native_decide`, no axiom beyond the three every Lean proof may use (`propext`, `Classical.choice`,
`Quot.sound`: `#print axioms` on each theorem).

| Property | Theorem | Holds for every reachable state of every instance with | Quint + TLC, 2 agents |
|---|---|---|---|
| S1 | `oneWorker_of_reachable` | `release = .idle` (PR #111) | 883,023 states, 217 s |
| S2 | `noEarlyStart_of_reachable` | `claimChecksDeps` (PR #112) | stopped at 30 min, unfinished |
| S3 | `locksDisjoint_of_reachable` | `lockOverlap` (PR #114) | 4.05M states, 577 s |
| S4 | `inboxExact_of_reachable` | `deliverCas` (PR #115) | stopped at 30 min, unfinished |
| S5 | `doneHasEvidence_of_reachable` | `evidenceRequired` (PR #113) | 13.9M states, 625 s |

Each theorem is for any sizes and any setting of the other switches, `racy` included. A TLC run that finished
covered 2 agent slots, 1 to 3 tasks and a bounded log; the four that hit the 30-minute cap had seen 23M to 92M
states, and no liveness check got past the first instance.

What carries each proof:

- **S1**: an agent that believes it holds a task does hold it, or the task was dropped, or the agent isn't at
  work and has an unread `released` message for it; and no two agents have a belief that isn't of that last,
  stale kind (`J`). Reap under PR #111 reopens a claim only when its owner isn't at work, and tells it; every
  way back to work delivers the inbox first. It needs S4's "no cursor passes a message it didn't show", which
  holds with or without PR #115, and that `task add` never reuses an id (`Pfx`).
- **S3**: a lock's holder is live, and unexpired locks of different agents share no file (`LkInv`).
- **S4**: per agent, what was shown is in order and behind the cursor, everything behind the cursor since the
  spawn was shown, and the waiter's snapshot skips nothing between the cursor and its last id (`Inb`).
- **S2**, **S5**: the ghost flag stays off; done implies evidence.

Liveness: `deadLive_not_stuck` is L4's part (with watchd running, `hc ls` answering and the row bound, a dead live row always has the reap enabled). L2 is proved over fair runs. A run is a sequence of steps (`Run` in `Fair.lean`); it is fair (`Run.Fair`) when
every action of `fair` that is enabled at infinitely many steps happens at infinitely many steps (strong
fairness; weak fairness is not enough for L1, see below). `idleClaim_leads_to`: in a fair run of an instance with
`racy = false`, `release ≠ .ended` (PR #110 or #111), `watchd`, the agent and the task in the instance, no `bgStart` or `die` in the run, and the agent with no job and a live terminal at the start, a state where an
idle agent holds a claim is followed by one where it doesn't: the lease lapses (`expire`), the tick reopens the task
(`tick_reopens`) or the owner gets back to work. A slot a spawn refills is a new agent: it boots at once (the proof
shows `boot` happens), so it doesn't count. The proof is two persistence lemmas (`persist`, `tick_persist`: while an
idle agent holds the claim, a lapsed lease stays lapsed and a booting agent keeps booting) and fairness of `boot`,
`expire` and `tick`. `racy` is left out: the race splits are for S2 and S4.

Not proved: **L1** and **L3**. Both need strong fairness of `claim` (a working agent that keeps coming back to an
empty inbox takes the work; weak fairness lets two agents post to each other forever, so neither's `claim` is
continuously enabled) and `roster ≤ nagents`. L1 also needs the digest/wake/claim chain of a reusable agent and a
bound on digests (`told` only grows). L3 needs that a reopened task is taken, which is L1 for the slot its owner's
end frees. No fair run is shown to exist (strong fairness could be unsatisfiable in principle), so the theorem could
in principle be vacuous; the runs of findings #1, #3, #8, #9 still show the three properties fail without the fixes.

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
| 10 | work lost | `bgKeeps := false` / the run | An agent claims a task, starts a long background job (CI wait, model check) and stops; the lease lapses, reap reopens the task as its owner is idle, and watchd spawns a fresh agent onto it while the job runs (seen on #107). | PR #121 (board #115) |
| 11 | work lost | `retake := false` / the run | The task is reopened; its owner, whose context is past 350k, comes back and `task claim` refuses it, so only a fresh agent can take it. | PR #121 (board #115) |
| 12 | work loss | `allWts := false` / the run | An agent owns two worktrees; `wt_map` picks the landed one, the other holds work not on main, and lifecycle ends the agent mid-task. | PR #123 (board #116) |
| 13 | stuck, silent | `uncleanNudge := false` / the run | An agent idle 30 min with an unclean worktree and nothing else holding it: no action is enabled, forever, and nobody is told. With the fix `nudge` is enabled and its urgent message wakes the waiter; a second nudge is refused until the agent has woken and stopped again. | PR #122 (board #114) |

Findings 10 to 13 are runs only: no theorem says lifecycle never ends an agent with unlanded work, or that the nudge makes the agent clean (it can ignore it). 
| 14 | L4 | `watchd := false` / `deadLive_not_stuck` | An agent holding #1 loses its terminal. With no watchd nothing ends the row: `swarm who` and `swarm post` show it gone, but it stays live, keeps its claim, and a message to it is stored unread. | open: run watchd, or end the row by hand (`swarm leave` is the agent's own) |
| 15 | L4 | `hcSees := false`, or `unbound := [0]` / `deadLive_not_stuck` | watchd runs but can't tell. The dead agent was working, so reap keeps its claim past the lease (`keeps`: the owner isn't idle) and #1 stays claimed forever. An unbound row is a communicator that joined from outside hc; `hc ls` failing makes `live_addrs` nil for every row. | open |

Nothing else is open: every other counterexample above has a fix on main. #14 and #15 are not fixed.

The notices to the communicator are not rows of the model, so "a notice for the communicator reaches a live one, or
its sender is told" is read from the code, not proved: watchd posts its notices (`lease-late`, `blocked on #N`, idle
unclean worktrees, quiet) to the communicator's name, `msgs.post` stores them whether or not that row is live, and
only `swarm post` says anything of the recipient (`no terminal; can't be delivered now`, from `hc ls` at read time).
So a notice to a dead or unbound communicator, or posted before its terminal died, reaches no one and tells no one:
the same two causes as #14 and #15, and the sender of a notice is watchd.

## What is proved, what is replayed, what isn't modelled

**Proved**: S1 to S5, as *Results* says, of the model. A proof is about `Model.lean`; that the model is the code
is what the replay tests. **Evaluated**: the thirteen counterexamples and their fixed runs. **Not proved**: L1, L3 and L4 as statements about fair runs (L2 is, for `racy = false`).

**Replayed** (random, not exhaustive): that the model is the code. Each step of a run does the command it stands
for (`task claim`, `lock`, `post`, `hook stop`, `swarm wait`, `watchd --once`, …) or, for time and the world,
writes the db (`lease_until` in the past, `last_active` back 200 s or 4000 s, `ctx_tokens`, the waiter's pid:
the test's own while the model's waiter is alive, none once it is gone), and then the db must match the model:
every task's state, owner, live lease, evidence and answer; every agent's status; every lock; every message to
an agent, in order; and each agent's unread list. The 12 committed runs (seed 107, 50 steps) are in the Lua
suite; `replay.sh 60 40` does 60 fresh ones in about 2 minutes.

Replayed with `racy` off and no hc: a race can't be forced through the CLI, and `hc` isn't faked in the replay.
Those parts (S1's hc prompt, S2's and S4's races) are proved of the model and not replayed.

**Not modelled**: the red-main task and CI; conflict notices and the edit hook; `swarm run` and machines;
git itself: an agent's worktrees are two flags (`wt1`, the one `wt_map` picks, and `wt2`) that `dirty` sets and clears
at will, `stale` (idle 30 min) is an action that is not in `fair`, a nudge needs a live waiter (the no-waiter notice to
the communicator is a notice), and none of this is replayed through the CLI (`Traces.lean` doesn't generate `dirty`,
`stale` or `nudge`: PR #122's and #123's behaviour is covered by `cli_lifecycle_spec.lua`); another swarm's communicator on the board (PR #124); roles and `swarm stay`
(no model agent stays, so lifecycle may end any of them); staffing limits beyond the roster; auto-spawn's
launch failures, backoff and halt; the handoff and the fence's other half (ctx_tokens is a model bit, `big`, set when the agent stops); the background job is a flag that starts and ends (the Lua reads processes: `machine.bg_agents`); `reaped` forgets a reap once another agent claims, so after a manual release by the retaker the Lua still lets it retake and the model does not; compaction
(`compacted_at`: the model's log only grows); death in the middle of a split command (`die` needs none pending); notices to the communicator; the 9000-character delivery budget
(every delivery shows all unread); `swarm join` (an ended agent never returns; its slot is a new agent); several waiters at once; the
`@all` channel; the hc terminal's own status (only its prompts are modelled, as watchd sees them).

## Running

```sh
swarm/model/check.sh            # every theorem and counterexample, about 12 s
swarm/model/replay.sh 60 40     # 60 fresh 40-step runs through the CLI
luajit swarm/lua/test/run.lua cli_model   # the committed runs (also part of the whole suite)
```

`check.sh` and `replay.sh` need `lake` (elan) on the PATH, or nix, which they use to fetch it
(`nix shell nixpkgs#elan`). The Lua suite needs neither.

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
| `SwarmModel/Findings.lean` | the counterexamples as runs (and findings #16 and #17, lassos; #18 to #21, W1-W4 on the current `Cfg`), and the same runs with the fix on |
| `SwarmModel/Liveness.lean` | L2 and L4 in one state: `idleClaim_not_stuck`, `deadLive_not_stuck` |
| `SwarmModel/Fair.lean` | fair runs (`Run`, `Run.Fair`) and L2 over them: `idleClaim_leads_to` |
| `SwarmModel/Taken.lean` | L1 over fair runs: `startable_leads_to` (and `startable_taken`, `ready_step`, `tick_ready`, `lifecycle_fills` it is built from) |
| `SwarmModel/Boot.lean` | L3, the reopened half: `booting_reads` (with `bootFirst`, a spawned holder reads the answer at its first turn) |
| `SwarmModel/Workspaces.lean` | W1-W4 and B1 (sw-bases) as statements, and their refutations (`not_B1`; `B1_of`: B1 with `perTaskBase`) on the current `Cfg` (`not_W1_branch`, `not_W1_proc`, `not_W2`, `not_W3_formal_wt`, `not_W3_formal_agent`, `not_W4`); `forever_of_loopOk` makes a two-state loop a fair `Run` |
| `SwarmModel/Comms.lean` | the communicator: several swarms (`World`, each swarm a `State`), hc terminals with a Herdr space, each swarm's communicator row and watchd (`CCfg`, `cstep`, `CReachable`); C1 and `C1all` as statements; `tick_binds_none`. The refutations (`not_C1_shared`, `not_C1_dead`, `not_C1_space`, `not_C1all_fixed`) are in `Findings.lean` |
| `SwarmModel/Holder.lean` | L3, the holder half over fair runs: `holder_leads_to` (and `pa_step`, the per-action step lemma, and `unblock_pa`) |
| `SwarmModel/Gone.lean` | L4 over fair runs: `deadLive_leads_to` (and `Rz`, `rz_of_reachable`: with `racy = false` no agent is between a read and its write) |
| `SwarmModel/Exists.lean` | non-vacuity: `lasso_run` (a lasso whose cycle takes every fair action enabled in it is a fair `Run`) and `fair_run_exists`, a fair run of `replay` meeting L1-L3's side conditions |
| `SwarmModel/Answer.lean` | L3 over fair runs, one statement per task: `answer_reaches`; `L3I`, the invariant the halves took as hypotheses (`l3_of_reachable`); `owner_step` |
| `SwarmModel/Traces.lean` | writes random runs of the `replay` instance as JSON, and the scripted runs (`script`) |
| `check.sh` | builds the model, which checks every theorem and run; fails on `sorry`, `native_decide` or an axiom |
| `replay.sh [n] [steps] [seed]` | `n` fresh runs, each replayed through the CLI |
| `traces/*.json.gz` | 12 runs of 50 steps (seed 107) and 4 scripted runs the Lua suite replays |
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
  worktree `wt_map` picks (agent.wt, else the one with its branch), or since PR #123 in any it owns. `sweep_worktrees`
  removes a worktree no live agent's agent.wt or `wt_map` names, with no process inside, untouched 30 min, clean and
  landed; `end_agent` removes the ended agent's `wt_map` worktree unless a live peer's agent.wt is it, if it is clean
  (git refuses a dirty one), whatever process is inside. Both then `branch -D` the branch it had checked out, unless it
  is `main`: a base like `formal` goes too. The base is `main` everywhere: `nbases > 1` is the swarm that lands elsewhere.
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
| `perTaskBase` | the landed checks (lifecycle, sweep) ask main only | sw-bases, board #3 (in the Lua, `bases.lua`): lifecycle asks the bases of the tasks an agent owns (`abases`; `Cfg.taskBase` gives each task's, main if none), the sweep every base a task names and main (`pbases`); `B1`, `B1_of`, finding #22 |
| `splitGC` | end_agent removes the ended agent's worktree, looking at no process; sweep runs `branch -D` on whatever was checked out but main | sw-bases, board #4: ending kills the terminal only; the sweep checks reachability from a protected ref itself and deletes only a branch that is no base and is reachable |
| `recordedWorkspaces` | an agent may check out a base in its worktree | sw-bases, board #5: swarm creates and records worktrees; a checkout of a base is refused |

`perTaskBase` is in the Lua (board #3) and `replay` has it on (tasks 2 and 4 on `formal`); the other two are the fix sw-bases proposes, defined but not yet in the Lua or proved (board #6).

The communicator's world (`Comms.lean`) has its own switch, `CCfg.ensureComms`:

| Switch | Before | After |
|---|---|---|
| `ensureComms` | `swarm join` refuses only a live binding of the same row elsewhere; reap ends a communicator row whose terminal is gone and nothing binds a new one; auto-spawn opens tabs in the space of watchd's own terminal | board #9: watchd's tick launches a communicator in the swarm's space when the swarm has work and none is bound to a live terminal there whose session is it; auto-spawn launches into the swarm's space; `join` refuses a terminal outside the swarm's space, and one that is another swarm's communicator unless `--takeover` |

Defined, not yet in the Lua or proved (board #9, #10).

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

Workspaces (sw-bases; `Workspaces.lean` states each as a `Prop`). The protected refs are the bases (`Cfg.bases`: main,
and a swarm's own such as `formal`); `Git.safe` is reachability from one, checked the way workspace GC must check it
(an ancestor, or the same content under a squash), never by `git branch -d`:

- **W1** A worktree is removed only if it is clean, unattached (no live agent's agent.wt or `wt_map` pick), no process
  is inside and its HEAD is reachable from a protected ref; a deleted branch is no protected ref and its tip is
  reachable from one. `gcOk`, of each step
- **W2** Ending an agent removes no worktree and deletes no branch: a tick does to git only what the sweep does.
  `endKeepsGit`
- **W3** On a fair run no worktree stays an orphan forever (there, clean, on a protected ref, unattached, no process,
  untouched 30 min: `orphan`), and no agent stays idle and free with its work on a base forever (`doneOnBase`)
- **W4** No worktree has a base checked out, so landing on a base is never refused for it. `noBaseOut`

All four fail on the current `Cfg` (findings #18 to #21, proved: `Workspaces.lean`). None holds today in a weaker form
worth stating: W1 fails even with main the only base (#18b).

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
`waiterGone` or `reapGone` (an agent that leaves, dies or loses its waiter can't be waited for). Then some state of the
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
The same cycle is fair with sw-bases' switches on; with agent 1's claim left out it is not (the check bites). It shows the
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
| 10 | work lost | `bgKeeps := false` / the run | An agent claims a task, starts a long background job (CI wait, model check) and stops; the lease lapses, reap reopens the task as its owner is idle, and watchd spawns a fresh agent onto it while the job runs (seen on #107). | PR #121 (board #115) |
| 11 | work lost | `retake := false` / the run | The task is reopened; its owner, whose context is past 350k, comes back and `task claim` refuses it, so only a fresh agent can take it. | PR #121 (board #115) |
| 12 | work loss | `allWts := false` / the run | An agent owns two worktrees; `wt_map` picks the landed one, the other holds work not on main, and lifecycle ends the agent mid-task. | PR #123 (board #116) |
| 13 | stuck, silent | `uncleanNudge := false` / the run | An agent idle 30 min with an unclean worktree and nothing else holding it: no action is enabled, forever, and nobody is told. With the fix `nudge` is enabled and its urgent message wakes the waiter; a second nudge is refused until the agent has woken and stopped again. | PR #122 (board #114) |

Findings 10 to 13 are runs only: no theorem says lifecycle never ends an agent with unlanded work, or that the nudge makes the agent clean (it can ignore it). 
| 14 | L4 | `watchd := false` / `deadLive_not_stuck` | An agent holding #1 loses its terminal. With no watchd nothing ends the row: `swarm who` and `swarm post` show it gone, but it stays live, keeps its claim, and a message to it is stored unread. | open: run watchd, or end the row by hand (`swarm leave` is the agent's own) |
| 15 | L4 | `hcSees := false`, or `unbound := [0]` / `deadLive_not_stuck` | watchd runs but can't tell. The dead agent was working, so reap keeps its claim past the lease (`keeps`: the owner isn't idle) and #1 stays claimed forever. An unbound row is a communicator that joined from outside hc; `hc ls` failing makes `live_addrs` nil for every row. | open |
| 16 | L1 (the pool) | `idleSlot` / `lassoOk`, `periodic` | Two tasks, a free slot, one agent. It takes #1, stops holding it, the lease lapses, the tick reaps it: the agent is idle with an unread `released`, so `reusable`, and lifecycle does not spawn into the free slot. It wakes, takes #2, and the same again. Every fair action enabled anywhere in the loop happens in it, and a startable task and a free slot are there at every state. L1 holds of each task (it is taken over and over), not of the pool. Evaluated for 4 periods; one more period changes only the log, the cursor and what was shown (`periodic`). **Not the real watchd**: the loop needs every tick to come after the lease lapsed (a tick while the agent holds a live lease would spawn onto the other task), and watchd ticks every 30 s against a 2 h lease; the model lets fairness delay a tick that long. | not a bug |

| 17 | L3 | `!answered` / `lassoP`, `periodicD` | Two slots, one task. Agent 0 blocks #1, goes idle big and cold, and the answer to it is a DM it never reads. Reap reopens #1, the tick ends agent 0 and spawns a new agent into its slot for #1; the answer is stored on the task but only that agent's first turn (`boot`) reads it. Before it boots its lease lapses and the next tick reaps it and spawns into agent 1's slot; agent 0 now boots (it holds nothing), goes idle big, and the same happens the other way round. Every fair action enabled anywhere in the period happens in it (`boot` and `age` included), and #1 is never open at a state, so no `claim` is enabled: a fair run in which the answer is never read. Evaluated for 4 periods; one more changes only the log, the cursor, what was shown and where inboxes start (`periodicD`). With the period's agent booting before its lease lapses (`[.boot 0]`) the answer is read. **Not the real timing**: a spawned agent holds a fresh 2 h lease and boots in seconds, so the loop needs a launch that hangs for hours, every time; the model has no time between a lease and a boot. | `bootFirst`: a boot beats a lease (`booting_reads`); not a bug |

| # | Property | Switch off / what holds with it on | The counterexample | Fixed by |
|---|---|---|---|---|
| 18 | W1 | `splitGC := false` / the run (W1 itself is board #6) | Agent 0 lands its commit on `formal` and on main, checks `formal` out in its worktree and leaves. 30 min on the sweep finds the worktree clean, unused and on main, removes it and runs `git branch -D formal`: the swarm's base is gone (`not_W1_branch`; the replay's `script-sweep` is the Lua doing it). With `splitGC` the sweep removes the worktree and keeps `formal`. | open: board #4 |
| 18b | W1 | `splitGC := false` / the run | end_agent looks at no process: agent 0's work is on main, a process sits in its worktree, it stops and ages, and the tick ends it and removes the worktree under the process (`not_W1_proc`). | open: board #4 |
| 19 | W2 | `splitGC := false` / the run | By design today: the same run with no process. The worktree was touched within 30 min, so the sweep keeps it, but the tick that ends agent 0 removes it and deletes its branch (`not_W2`). With `splitGC` the tick ends the agent and leaves git alone. | open: board #4 |
| 20 | W3 | `perTaskBase := false` / the run | A base that isn't main (the notapki `formal` swarm). Agent 0 lands on `formal` and leaves: its worktree is clean, unused, untouched, on a protected ref, and never swept, since the sweep asks main (`not_W3_formal_wt`). Or agent 0 claims #1, lands it on `formal`, marks it done and goes idle: lifecycle asks main, so it is never ended (`not_W3_formal_agent`; if it goes stale, the unclean nudge wakes it once per idle stretch, forever). The fair run: agent 1 starts and ends a background job over and over, and no other fair action is enabled (`loopOk`, `forever_of_loopOk`). The replay's `script-formal` is the Lua keeping both. With `perTaskBase` the tick removes the worktree and ends the agent. | open: board #3 |
| 21 | W4 | `recordedWorkspaces := false` / the run | Agent 0 checks out `formal` in its worktree; agent 1's commit can no longer land on it (`git push . HEAD:formal` is refused while a worktree has it checked out) (`not_W4`). With `recordedWorkspaces` the checkout is refused. | open: board #5 |

| 22 | C1 | `ensureComms := false` / the run (C1 itself is board #10) | One terminal is the communicator of two swarms (2026-11-10: sk-comms and fm-comms both on t87, in the notapki space). fm-comms joins swarm 1 from t87, then sk-comms joins swarm 0 from the same terminal: bind looks only at swarm 0's own row. The session is sk-comms now, its `swarm wait` reads swarm 0's db, and swarm 1's notices are stored and read by no one; swarm 0's communicator also sits outside its space (`not_C1_shared`). With `ensureComms` the second join is refused, with `--takeover` too. | open: board #9 |
| 23 | C1 | `ensureComms := false` / the run | The communicator's terminal dies and the swarm runs on. Watchd runs from another terminal of the swarm's space; agent 0 blocks #1 and the communicator's terminal dies. The tick reaps its row, and no tick ever binds a new one (`tick_binds_none`), so the notice that #1 is blocked goes to a name no one reads (`not_C1_dead`). With `ensureComms` the tick launches a communicator in the swarm's space. | open: board #9 |
| 24 | C1 | `ensureComms := false` / the run | Watchd started from a terminal in another space spawns there: launch.sh opens the tab in the space of `HC_TERMINAL_ID`, which for auto-spawn is watchd's terminal (`not_C1_space`). With `ensureComms` the spawn lands in the swarm's space. | open: board #9 |

Nothing else is open: every other counterexample above has a fix on main. #14 and #15 are not fixed; #18 to #21 wait for the sw-bases fix (board #3 to #6); #22 to #24 for `ensureComms` (board #9, #10). #16 is a statement that is too strong, not a bug; #17 is the same for L3, and the model now says a boot beats a lease (`bootFirst`).

The notices to the communicator are not rows of the model, so "a notice for the communicator reaches a live one, or
its sender is told" is read from the code, not proved (C1 says a live one is there to read them after each tick): watchd posts its notices (`lease-late`, `blocked on #N`, idle
unclean worktrees, quiet) to the communicator's name, `msgs.post` stores them whether or not that row is live, and
only `swarm post` says anything of the recipient (`no terminal; can't be delivered now`, from `hc ls` at read time).
So a notice to a dead or unbound communicator, or posted before its terminal died, reaches no one and tells no one:
the same two causes as #14 and #15, and the sender of a notice is watchd.

## What is proved, what is replayed, what isn't modelled

**Proved**: S1 to S5, as *Results* says, of the model. A proof is about `Model.lean`; that the model is the code
is what the replay tests. **Evaluated**: the counterexamples and their fixed runs. L1, per task, L2, L3, per task, and L4 are proved as statements about fair runs, for `racy = false`, and `fair_run_exists` shows fair runs meeting their side conditions exist.

**Replayed** (random, not exhaustive): that the model is the code. Each step of a run does the command it stands
for (`task claim`, `lock`, `post`, `hook stop`, `swarm wait`, `watchd --once`, …) or, for time and the world,
writes the db (`lease_until` in the past, `last_active` back 200 s or 4000 s, `ctx_tokens`, the waiter's pid:
the test's own while the model's waiter is alive, none once it is gone), and then the db must match the model:
every task's state, owner, live lease, evidence and answer; every agent's status; every lock; every message to
an agent, in order; and each agent's unread list. The git steps run git in the fixture's repo (its main checkout
detached, a `formal` branch), and after them and every tick git must match too: every worktree there or not, its branch,
HEAD, `git status` clean or not and its mtimes (what sweep reads); every branch's tip; each live agent's agent.wt. A
process inside is a `sleep` started there; 30 min is an mtime set back. The 12 committed runs (seed 107, 50 steps) and
three scripted ones (`script-end`: a squash-merged worktree is landed by content, its agent ended and the worktree and
branch removed; `script-sweep`: a fast-forwarded one swept, and one with `formal` checked out swept with `formal`; `script-formal`: worktrees whose work is on `formal` only
are kept, by the sweep and by lifecycle) are in
the Lua suite; `replay.sh 60 40` does 60 fresh ones in about 2 minutes.

Replayed with `racy` off and no hc: a race can't be forced through the CLI, and `hc` isn't faked in the replay.
Those parts (S1's hc prompt, S2's and S4's races) are proved of the model and not replayed.

**Not modelled**: the red-main task and CI; conflict notices and the edit hook (but for agent.wt); `swarm run` and machines;
of git: `origin` (the replay has none, so `main` is the base), `gh`'s merged-PR check, rebases, an agent removing its own
worktree, editing in a worktree it doesn't own or in the main checkout, merge conflicts; the unclean nudge is the action
`nudge`, not part of the tick as in the Lua: `stale` (idle 30 min) is an action that is not in `fair`, a nudge needs a
live waiter (the no-waiter notice to the communicator is a notice), and none of it is replayed (`Traces.lean` doesn't
generate `stale` or `nudge`, nor `cool` for an agent its unclean worktree keeps, since 4000 s idle is past 30 min and
the Lua's tick would nudge it: PR #122's behaviour is covered by `cli_lifecycle_spec.lua`); another swarm's communicator on the board (PR #124); roles and `swarm stay`
(no model agent stays, so lifecycle may end any of them); staffing limits beyond the roster; auto-spawn's
launch failures, backoff and halt; the handoff and the fence's other half (ctx_tokens is a model bit, `big`, set when the agent stops); the background job is a flag that starts and ends (the Lua reads processes: `machine.bg_agents`); `reaped` forgets a reap once another agent claims, so after a manual release by the retaker the Lua still lets it retake and the model does not; compaction
(`compacted_at`: the model's log only grows); death in the middle of a split command (`die` needs none pending); notices to the communicator; the 9000-character delivery budget
(every delivery shows all unread); `swarm join` (an ended agent never returns; its slot is a new agent); several waiters at once; the
`@all` channel; the hc terminal's own status (only its prompts are modelled, as watchd sees them).
Of the communicator (`Comms.lean`): the swarms share nothing but terminals (a worker agent's own terminal is the model's
`die`, not a `Term`); `hc ls` always answers and lists the communicator's terminal right; a launch never fails; a
session's ListAgents name is its `SWARM_NAME`, set by its last join; `swarm watchd --takeover` and a second watchd (board
#18); the human's `swarm spawn` (only watchd's spawns are placed: the starting roster is in the swarm's space). None of
it is replayed: the replay has no hc.

## Running

```sh
swarm/model/check.sh            # every theorem and counterexample, about 12 s
swarm/model/replay.sh 60 40     # 60 fresh 40-step runs through the CLI
luajit swarm/lua/test/run.lua cli_model   # the committed runs (also part of the whole suite)
```

`check.sh` and `replay.sh` need `lake` (elan) on the PATH, or nix, which they use to fetch it
(`nix shell nixpkgs#elan`). The Lua suite needs neither.

# /swarm: design synthesis (draft)

Synthesis of the four research lanes in `research/`, 2026-11-07:

- [sw-prior](research/sw-prior.md): what people have built.
- [sw-pitfalls](research/sw-pitfalls.md): failure modes and evidence.
- [sw-comms](research/sw-comms.md): the communication design space.
- [sw-substrate](research/sw-substrate.md): what to build it on here.

The lanes read sources through WebFetch, which returns summaries. Check exact
figures against the linked source before quoting them.

## The one-paragraph answer

The bottleneck in `/orchestrate` is the orchestrator's **attention**, not its
**authority**. Every frontier-model swarm that shipped code at 10+ agents
replaced manager attention with three things:

- **structure:** a shared ledger of work that agents pull from;
- **watchers:** deterministic scripts that route each event straight to the
  agent that owns it;
- **gates:** CI, oracles, and reviewers with a fresh context.

None of them replaced it with chat. None of them was flat in how *work gets
allocated*; several were flat in how *agents talk*. So `/swarm` should make
communication flat and keep allocation structured: anyone can talk to anyone,
create tasks, or take a task. Claims, leases, verification and merging follow
rules, not negotiation.

## What the evidence says (headline findings)

1. **Peers negotiating their own work failed with frontier models.**
   - Cursor's equal-status agents on a shared file with locks ran 20 agents
     at the throughput of 2–3.
   - With optimistic concurrency instead of locks, they became risk-averse,
     and "no agent took responsibility for hard problems".
   - Planners, workers that never talk, and a judge per cycle worked at
     hundreds of agents.
2. **Flat with no messages at all worked** in Anthropic's C compiler run: 16
   Opus 4.6 agents, git lock files, a near-perfect test oracle, about $20k.
   It collapsed when every agent hit the same bug, and was fixed by changing
   the oracle so the work split up, not by adding communication.
3. **Anthropic's August 2026 flat-forum swarms of 10–80 agents** split by task.
   - Exploration won: 266 vulnerabilities found against 21 for independent
     agents.
   - Building lost: merge rates fell as the swarm grew, and the games were
     poor.
   - Agents conformed: 18 of 30 picked the same branch name.
   - Agents that didn't know about each other sabotaged one another.
   - Role and "CEO" *prompts* changed nothing. Only structure did.
4. **Errors spread fastest with no checker.** In Google's study, independent
   agents amplified errors 17.2× and peer debate 7.8×, against 4.4× with one
   verifier. In the AI Village, one hallucination spread to every agent
   through sycophancy.
5. **A message costs the receiver its context.** A message to an idle Claude
   Code session starts a turn that re-sends its whole context. Broadcasting to
   N agents with 150k-token contexts costs N × 150k tokens. Coordination turns
   grow about n^1.7.
6. **The merge pipeline breaks before the agents do.** Yegge at 40+ agents:
   the merge queue passed 100 MRs, so he moved to megabatch merges and about
   45 cron watchers ("crons watch, models act").
7. **Nobody has tried rooms for coding.** Breakout rooms with movement are
   the novel experiment here, with no prior art to lean on.

## Design principles for /swarm

1. **The board is the backbone; messages are for exceptions.** Tasks, claims,
   status and decisions live in one durable store. Messages carry blockers,
   design questions and discoveries ("look at X"). They never carry status.
2. **Pull by default, push only to unblock.** Agents read the board and their
   rooms or channels at breakpoints: after a task, before a push, when
   blocked. Waking someone is the expensive act.
3. **Pure flat (user decision, 2026-11-07).** The skill defines no roles.
   Agents decide among themselves who plans, reviews or builds, as lanes do
   under /orchestrate. Roles are a later experiment if the baseline shows
   unowned hard work, as Cursor's flat runs did.
4. **Rules beat negotiation for contention.** Claims are leases that a script
   reaps when they expire. Hotspot files get one owner. Ties break by name
   order. In DPBench, one round of chat barely reduced deadlock; an ordering
   rule cut it to 0.
5. **Gates replace the manager's judgment.**
   - Nothing reaches "done" without evidence: a command, a CI link.
   - Reviewers get a fresh context, and a different model where possible.
   - A claim one agent makes without evidence is a rumor to the others.
6. **Watchers replace the manager's attention.** One deterministic daemon
   watches CI, PRs, `hc` status, stale leases and queue depth. It routes each
   event to the **owner**, not to a hub. This is `orchestrate/watch.sh`,
   pointed at owners instead of the orchestrator.
7. **De-correlate the agents.**
   - Every agent starts with its own area and the roster, so no two get
     identical prompts.
   - Claim and branch names include the agent's name.
   - Mix models where a decision matters.
8. **Keep the communicator's cost flat as N grows.** It reads state and
   digests, never traffic. It steers by writing where agents already pull
   from: the board, then `#announce`, then joining a room, then `@all`. It
   hears only about `blocked-on-human` and design decisions.
9. **Swarm only work that splits.** Use it for many files, an oracle, or a
   test corpus. Strictly sequential work lost 39–70% with multiple agents;
   use one agent with subagents for that.

## v1 architecture (sw-substrate's recommendation, adopted)

| Part | What | Reuses |
|---|---|---|
| Members | Herdr tabs via `relaunch/launch.sh`. Everyone runs `--permission-mode auto` with `crossSessionInbound: accept`; mixed mode classes hold messages, then drop them after 5 min. `--model` is set per agent. | launch.sh, orchestrate model table |
| Store | `.swarm/swarm.db` (SQLite WAL, gitignored, absolute path shared by worktrees). Tables: see "What's built". | — |
| CLI | `swarm` (python3 stdlib): see "What's built". One Bash call per post, whatever the fan-out. | — |
| Delivery to busy agents | A `PostToolUse` hook injects the agent's unread items as `additionalContext` at its next tool round. | hooks |
| Waking idle agents | A `Stop` hook with `asyncRewake` runs `swarm wait --me X` and exits 2 when something arrives. **Unproven: probe first.** Fallback: whoever posts gets a list of idle recipients and sends each a one-line `SendMessage` nudge. | — |
| DMs | `SendMessage`. A `PostToolUse` hook mirrors each one into `msg`, so the human sees it. | — |
| Watcher | A daemon (not an LLM); what it does now is under "What's built". It writes each event to the owner's inbox in `swarm.db`, and the hooks deliver it. | watch.sh, merge-retry.sh, overlap.sh |
| Human view | Herdr's Swarm panel (`swarm/herdr`, from `swarm state --json`); `swarm watch`, a colored log tail in a split, where the panel isn't installed. Zero model cost. | herdr-app |
| Communicator | `<prefix>-comms`, an ordinary member in `#human` and `#announce`. It writes goals as tasks, reports `blocked`, and relays the judge's verdict. Agents never `hc send` it. | orchestrate's reporting norms |
| Ending | The board decides. A fresh-context judge checks the written definition of done each cycle. The communicator asks the human before ending the swarm. | — |

Considered and rejected for v1:

- **Agent teams:** fixed lead, no nesting, panes only in tmux or iTerm.
- **`hc send` as transport:** it arrives as *user* input.
- **MCP channels:** a research preview with a dialog at every launch; a v2
  candidate.
- **GitHub issues as the board:** rate limits, too slow for chat.

Capacity here, measured: about 300 MB per `claude` process, so 50 fit in RAM.
Plan quota and the agents' own builds are the real limits. Plan for "dozens
registered, 8–15 working at once", with parked agents woken by messages.

## Experiments, in order

**Phase 0: probes** (an hour or two, one agent).

| Probe | Question it answers |
|---|---|
| asyncRewake waiter | The timeout ceiling, and what happens at expiry. This decides between hook wakes and SendMessage nudges. |
| Wake cost | 20 DMs to an idle agent with a big context; read `/usage` before and after. |
| Classifier screening | Does auto mode screen cross-session messages, and does it block terse peer messages? |
| Socket posting | Can a script post to a session's messaging socket? The format is undocumented, so this would be unsupported anyway. |

**Phase 1: Design A, "board + DMs".** The control: no rooms and no channels.
Run 5 agents on one real decomposable task in one repo. This is the baseline
closest to the C compiler run.

**Phase 2: switchable comms layers on the same task**, at N = 5 and 15:

- **B, pull channels:** topic channels with stewards who write digests.
- **C, rooms with movement:** at most 5 per room, one room per agent. A
  convener closes the room with a decision record on the board. The
  communicator can drop in.

**Phase 3: D, self-forming cells with temporary leads**, at N = 30.
`lead/<area>` is a claimable role with a charter and an exit condition. It
must be enforced structurally (workers see only their cell's tasks), because
prompts alone did nothing in Anthropic's runs.

**Metrics.** Almost all come from the db, git and CI, without asking agents
anything:

- merged PRs per wall-hour;
- tokens per merged PR;
- wakes per agent-hour;
- communicator tokens as N grows (should stay flat);
- duplicate work;
- stale claims;
- idle agents while open work exists;
- question → decision latency;
- human directive → agents acting on it;
- retracted claims that others had acted on;
- reverts and red main after merges.

## Relation to /orchestrate

Kept as is:

- `launch.sh` and the lane rules on background jobs, zsh, pipes, worktrees,
  branch hygiene and relaunch;
- `watch.sh`'s CI logic, `merge-retry.sh` and `overlap.sh`;
- model-per-kind-of-work;
- "peer messages aren't the user."

Changed:

- Reports go to the board, not to a person.
- The watcher routes to owners.
- Merging moves from the orchestrator to a gate (see decision 2).
- The communicator replaces the orchestrator and never sits in the event
  path.

## Decisions (user, 2026-11-07)

1. **Pure flat.** No roles in the skill.
2. **How work lands is per repo, not in the skill.** The skill says "land
   work the way the repo's CLAUDE.md and `.claude/orchestration.md` say".
   jk_ledger and linn-studio already push to main after a rebase, with CI on
   main and the agent that broke it fixing forward, so agents land their own
   work there. A repo that needs human review keeps its PR flow.
3. **Baseline first** (Design A: board plus DMs, plus file-touch visibility).
   Choose rooms or channels after seeing where it struggles.
4. **Target: jk_ledger.**
5. **12 agents.**

Added 2026-11-07, after the first live run (sr-* on this repo, jk_ledger next):

6. **Information, not gates.** Contention is resolved by telling agents what
   is true at the moment they decide (a machine note, a conflict notice), not
   by slots, queues or timers. `swarm heavy` is removed.
7. **No time windows.** The 60-minute touch window is gone: a conflict is a merge that fails now, and a lock is freed when
   the holder's work lands.
8. **The task body is the request.** Agents build every item it lists and
   say in the PR why one is wrong; the communicator steers by editing the
   board, not by DMing claimed work.

## What's built

The v1 spec that stood here (touch notices, leased locks, `swarm heavy`,
the `role` table) is replaced by the code and by the specs below. Read those for
the mechanism; this section only says what each part is for.

Everything lives in `swarm/`, symlinked to `~/.claude/skills/swarm`: one
python3-stdlib CLI (`swarm/swarm`), `SKILL.md` for the communicator,
`brief.md` for agents (prepended by `spawn`), `settings.template.json` for
their hooks, and `test_swarm.py`. `swarm -h` lists commands.

### Store

`$SWARM_DB`, default `<git common dir>/swarm/swarm.db`, shared by every
worktree of the repo. Tables: `agent`, `msg` (`kind` includes `notice`),
`cursor`, `task` (with `after` and `model`), `lock`, `conflict`, `pairkey`
and an append-only `event` log for `swarm watch` and `swarm-retro`.

### Locks and overlap: [research/sw-locks.md](research/sw-locks.md)

- **Worktree attribution.** An agent's worktree comes from its edit paths
  (branch `<name>/…` as fallback). Editing inside a peer's worktree raises
  one `shared-tree` notice.
- **Trial-merge conflict episodes.** `watchd` snapshots each worktree and
  trial-merges pairs with overlapping files (`git merge-tree`). Only a real
  token-level conflict becomes an episode and one `notice` per agent; a
  line-only conflict that merges compatibly is logged as `conflict-compat`.
  Each side is the agent's own changes replayed onto `origin/main` (local
  `main` only if ahead), so commits merged in from main belong to no one; an
  agent whose own changes conflict with main is skipped (`conflict-stale`).
- **Reservation locks.** `swarm lock '<glob>'` or `dir/` reserves what git
  can't see, such as a migration number. Overlapping locks are refused; a
  lock frees itself when the holder's work lands.

### Lifecycle: [research/sw-lifecycle.md](research/sw-lifecycle.md)

- **`watchd` ends landed agents**: idle, no claim, no lock, work on main.
  It removes their terminal, worktree and branch. The communicator is exempt
  and does not end agents.
- **`watchd` spawns** a fresh agent per startable task when none is reusable,
  within `--max-agents` and `--min-free-mem`.
- **`task add --after N`** keeps a task unclaimable until #N is done; `task
  done` prints whether to take the next task or go idle.
- **Leases** are live: an expired claim reopens only when its owner has
  ended; a live owner is reported to the communicator, not overridden.

### Resources by information, not gates

- **Machine note** (`swarm machine`). The `PreToolUse` hook on Bash adds a short note to
  build and test commands (built-in patterns plus the repo's
  `.claude/swarm.json` `{"heavy": [...]}`): free memory, pressure (PSI), and
  which heavy processes run, attributed to agents. Context only, never a deny.
- **`watchd` machine tick.** Edge-triggered `pressure` / `pressure-end`
  events and one `notice` to agents running heavy processes;
  `oom_score_adj` 500 on agents' heavy processes so the OOM killer picks
  them before the dev db; kills of heavy processes orphaned in an ended
  agent's worktree.

### Pure flat

No roles in the skill. The communicator is an ordinary session that writes
tasks, runs `watchd` and relays questions for the human; it steers through
the board and never reassigns claimed work by message.

### Ownership: [research/sw-ownership.md](research/sw-ownership.md) (proposed, 2026-11-08)

Every fact with one holder (a task's owner and lease, a lock, an agent's
terminal, the communicator, watchd) changes under one rule set:

- **One change, one `begin immediate` transaction**, or one conditional
  update whose `rowcount` decides. No subprocess runs inside one.
- **The bound terminal is the fencing token.** Only `swarm join` moves
  `agent.hc`, and a live binding moves only with `--takeover` (logged).
  A command from another terminal is refused with the holder's name; a hook
  there writes nothing. A relaunched successor's one step is `swarm join --takeover`.
- **Intent before effect.** `swarm spawn <name> --task N` claims before it
  launches and rolls back if the launch fails.
- **Ended agents return only through `join`.**

This is ownership correctness, not rationing (decision 6). A second holder
makes the board wrong. The refusals name who holds what, and the rule
removes a timer (auto-spawn's one-interval wait).

### Hooks, delivery and the cold-cache rule

Unchanged from the design: `PostToolUse` delivers unread messages beside the
next tool result (capped), a `Stop` hook with `asyncRewake` runs `swarm wait`
to wake idle agents, and a non-urgent message to a cold agent (idle past the
cache window with a large context) is stored, not sent.

## Side observation from this wave

The four research lanes could send each other one-line pointers. They did,
and both sw-comms and sw-pitfalls cite findings that came from peers. No
lane waited on another, and the orchestrator was never in that path. That's
a small proof of principle for "pointers by DM, content in files".

# sw-roles: agents that choose their own role

Plan, 2026-11-09, against `swarm/` at 0455397. No code here; §8 is the build
split. Read with [DESIGN.md](../DESIGN.md) (decisions 1, 6, 7),
[sw-lifecycle.md](sw-lifecycle.md) §4.1 and [sw-ownership.md](sw-ownership.md) §4.

## 1. The request

An agent may be an implementer, an orchestrator, a reviewer, a designer, a
planner or anything else, and may switch as the work changes. The CLI and
watchd guarantee five things and impose no flow:

1. agents are tracked, so the user sees each one's status and role;
2. tasks are tracked when agents choose to take them;
3. messages arrive, and spawned agents are hooked into the swarm;
4. agents are nudged to keep working, or to clean up and end;
5. telemetry an agent can decide by: machine load here and on other
   machines (added by the user, 2026-11-09; §6a).

Today the only shapes are "hold a claim" and "be ended": watchd ends every
idle agent that owns no claim or lock once its work is on main
(`watchd.lua:371-385`). A reviewer waiting for PRs or an orchestrator between
decisions looks exactly like a finished implementer.

## 2. The answer in one paragraph

Two free-text fields on the agent row, both written only by the agent itself.
**`role`** is a label: what I am doing now. It is shown everywhere and decides
nothing. **`stay`** is one sentence: what I am waiting for. It is the one new
thing an agent can hold, beside a claim and a lock, and watchd does not end an
agent that holds it. An agent with no `stay` is judged exactly as today. So
"finished" stays mechanical (idle, holds nothing, work landed), and the only
new judgment, "am I still needed with no task?", is made by the one party
that can know: the agent. watchd adds one edge-triggered notice for stayers
when the swarm goes quiet. Nothing in the CLI or watchd ever reads the text of
a role.

Why a label plus a hold, and not role rules: DESIGN finding 3. Role prompts
changed nothing in the flat-forum runs; only structure did. The label is
information for the user and peers. The structure is what the agent holds
(`stay`, claims, locks) and the tools it calls (`task add`, `spawn`).

## 3. Data model and views

`agent.role text`, `agent.stay text`: two columns through `db.COLUMNS`, both
null by default. One line each, newlines stripped, cut at 80 characters on
write (peers read them, and peers are data).

| Command | Effect |
|---|---|
| `swarm role "<text>"` | Set my role. Logs event `role` (so the retro has the history; no history table). Prints who else declares the same text: "sr-4 also declares 'reviewer'". That is the whole answer to duplicate roles: information, not exclusivity (decision 6). |
| `swarm role` | Print mine. |
| `swarm stay "<what I wait for>"` | Set my stay. Logs `stay`. |
| `swarm stay --end` | Clear it. Logs `stay-end`. From then on I am judged as any agent. |

Both write through `agents.touch`, so they are fenced by terminal like every
other self-write, and both travel with the name through `join --takeover`.
`agents._release` clears `stay` (it is a held thing: an ended or reaped agent
holds none). `role` survives, as `model` does.

| View | Shows |
|---|---|
| `swarm who` | `sr-7 idle role=reviewer stays: "PRs for #130-#140" ctx=…` |
| `swarm board` | The owner's role beside a claim (`#107 claimed sr-92 (model checker)`), and one footer line per stayer: `staying: sr-7 reviewer: PRs for #130-#140`. Agents run `board` first, so this is where they learn who reviews or steers. |
| `swarm state --json` | `role` and `stay` on each agent (`state.lua:136`). |
| Herdr Swarm panel | Role as a chip on each agent row and in the detail view. An idle stayer reads "staying" with its sentence, not "idle", so it doesn't look dead. Event table entries for `role`, `stay`, `stay-end`, `quiet`. |
| Spawn brief roster | `sr-92 (idle, model checker)`. |

## 4. Lifecycle: idle, finished, staying

sw-lifecycle §4.1 gains one row and changes one:

| State | Test | Action |
|---|---|---|
| staying | idle, `stay` set | none; persists. One `quiet` notice per quiet edge (below). Never gets the task digest. |
| finished | as today, **and `stay` is null** | watchd ends it |

Code: one more term in the skip condition at `watchd.lua:371` and one more
`and stay is null` in `end_agent`'s re-check transaction (`watchd.lua:156`),
so an agent that ran `swarm stay` between the judgment and the kill is kept
(sw-ownership rule 1).

Everything else is unchanged and still right, because it now only ever sees
agents that did not ask to stay: `reusable`, `passed_over`, the digest, the
unclean nudge, auto-spawn. Leases stay task-only: `stay` protects the agent,
not its claims, so an idle stayer's expired claim reopens as today.

**A done agent must still be ended.** Three paths, no timer:

1. It runs `swarm stay --end` and stops. Today's rule ends it.
2. **The quiet notice.** The swarm is *quiet* when no task is open, claimed
   or blocked and no agent other than stayers and the communicator is live.
   On the edge into quiet (event `quiet`, re-armed by the next task add or
   claim, as `pressure`/`pressure-end` is), each stayer with a live waiter
   that is not cold-guarded gets one message: "The board is empty and nobody
   is working. You stay for: '<text>'. If that is over, `swarm stay --end`
   and stop; if not, carry on." The communicator gets one notice listing the
   stayers, which is also the "all tasks done, tell the user" signal it lacks
   today. A cold or waiterless stayer is not woken; it is named in that notice
   (the shape of `unclean`).
3. Its terminal dies: `reap` ends it as today.

A stayer that ignores the notice stays, visibly: `who`, the board footer and
the panel show the sentence and the idle age. The communicator can message
it. Nothing forces it out; see risks.

**Context.** `hook.ctx_advice` tells an agent at 350k to "finish this task,
then go idle; a fresh agent takes the next". For a stayer that is wrong: the
advice becomes the one the communicator gets today (hand off with `relaunch`
at 550k, pass on what you hold). The `comms` branch generalizes to "has a
stay". `task claim`'s refusal at 350k is unchanged.

**`task done`'s closing line** (`tasks.lua:296`) for a stayer: "you stay for
'<text>'" in place of "go idle … watchd ends you".

## 5. What assumes task-only agents today, and what each becomes

| Rule | Today | Becomes |
|---|---|---|
| `lifecycle` end (`watchd.lua:371-385`) | idle + no claim + no lock + landed = finished | adds "+ no stay" (§4) |
| `passed_over`, `reusable`, digest | an idle claimless agent exists to take tasks | unchanged; stayers never reach it |
| Auto-spawn per task | watchd staffs every startable task | unchanged and optional: it is the scripted orchestrator. A swarm whose orchestrator staffs tasks itself runs `watchd --max-agents 0` (works today). Both can run: `spawn --task` reserves, so they can't double-staff. |
| Leases, `reap` | claims only | unchanged |
| Communicator exemption (`is_comms` in `lifecycle`, the `*comms` name suffix) | a special case in code | the communicator is a stayer: `swarm watchd` sets its `stay` ("the user's channel") in the transaction that writes `meta.comms`. The lifecycle exemption and the suffix rule (`agents.lua:125`, `tasks.lua:315`) are deleted. `meta.comms` remains, as an address: where watchd sends what needs the human. That is the only role the CLI knows, and it knows it as an address. |
| `brief.md` | "There is no manager", "`swarm board` first … claim before you work", "Ending: after `task done` …" | §6 |
| `SKILL.md` | "Agents are peers with no roles"; the communicator spawns one agent per area | §6 |
| `swarm rules` | repo landing rules, written for implementers | unchanged mechanism. The communicator may put the user's wishes about roles there ("one reviewer per PR, a different model") as text. |
| DESIGN decision 1, principle 3, "Pure flat" | no roles in the skill | new decision 9: the skill still *defines* no roles; agents declare them. Phase 3's "claimable lead role, enforced structurally" is not built (§9). |

## 6. Spawn, brief and skill text

**Spawn.** `swarm spawn <name> --model <m> [--role "<text>"] [--stay "<text>"] [--task N] -- <brief>`.
Both flags are column writes at reserve/bind time (intent before effect): a
spawned reviewer is a stayer before its first turn, so it can't be ended in
the gap before it would have said so itself. The free text after `--` is
already the role brief; no role templates.

**Agents may spawn peers**, as the brief already says. That is what makes an
orchestrator possible. What's missing is information at that decision:
`swarm spawn` prints the live count, the count the user launched and free
memory before it launches. Whether the user's count also *refuses* is
question 1 in §10.

**brief.md** (kept short; each line lands with the PR that makes it true):

- Opening: "There is no manager unless a peer takes that role. The board and
  your peers' messages are how work gets allocated."
- New bullet **Role**: "Yours to choose and change: `swarm role "<few words>"`
  when what you do changes (implementer, reviewer, planner, orchestrator, …).
  `swarm board` shows everyone's. Taking tasks is one way to work, not the
  only one. If your work is not a task and you will sit idle between pieces
  of it, say what you wait for: `swarm stay "<what>"`, and watchd won't end
  you. `swarm stay --end` when it is over."
- **The board**: "`swarm task claim <id>` before you work *on a task*".
- **Talk at breakpoints** gains one allowed reason to post: a request to the
  peer whose role covers it ("PR #12 is ready" to the reviewer).
- **Ending**: "watchd ends you once you are idle, own no claim or lock, stay
  for nothing and your work is on main."

**SKILL.md**: "Agents choose their own roles; you assign none unless the user
asks." §1.4 shows two starts: the flat board (today, the default), and
seeding one strong-model agent with `--role orchestrator --stay "…"` and
`watchd --max-agents 0`. The communicator stays out of the event path either
way (principle 8): if the swarm wants an orchestrator, it is a separate agent.

## 6a. Telemetry: measured, not guessed from words

Revised 2026-11-09 on the user's word: the fixed list of build words goes,
and measurement replaces it.

### What goes

`machine.HEAVY_RE`, `NOT_HEAVY`, `is_heavy`, the `heavy` key of
`.claude/swarm.json`, the hook's heavy trigger (`hook.lua:134`), and the
`heavy-start` and `heavy-count` events. The list misses what it doesn't name
(a repo's own build script), flags what it does (`make help`), and can't see
size at all: `cargo test` of one crate and of a workspace look the same.

### Measuring every command: the candidates

Probed on this machine (Linux 7.3, cgroup v2, systemd user session):

| Means | Memory peak | CPU | Wall | Per command? | Cost and limits |
|---|---|---|---|---|---|
| **A. `/proc` on watchd's tick**: every process under an agent's `claude_pid` (what `heavy_procs` walks, minus the word filter) | sampled every tick (30 s): the largest sum of RSS over the command's process tree | the command shell's `cutime+cstime` at its last sample: exact for children it has reaped | first seen to last seen, within one tick | **yes**: each Bash-tool call is one shell under the claude process (the `shell-snapshots` mark `bg_agents` already uses), its argv ends in `eval '<the command>'`, and concurrent and background commands are separate trees | no setup, no hook, no schema; watchd already scans `/proc` each tick. Misses commands shorter than a tick and peaks between samples. Linux only. |
| **B. A cgroup per agent**, set at spawn | exact (`memory.peak`, kernel-kept) | exact (`cpu.stat`) | no | **no**: one number per agent lifetime. A per-command reset needs a held file descriptor or a cgroup per command, which is a command rewrite. | Today every hc terminal shares one cgroup (`hc-hold-….service`, 855 pids), so it gives nothing as is. `systemd-run --user --scope -- claude …` at launch works (probed: its own `memory.peak` and `cpu.stat`). Linux with systemd only. Also gives per-agent PSI and `cgroup.kill`. |
| **C. Hook timing** (PreToolUse to PostToolUse) | none | none | exact for foreground | yes, but **wrong for background commands**: PostToolUse fires when the command is put in the background, and long builds are run that way | no new process (the hooks already run), but it needs a table for open commands |
| D. eBPF, process accounting, taskstats | exact | exact | exact | yes | need root; not considered further |

Neither reaches work done by a daemon on the agent's behalf (`nix build`,
`docker build`): that runs outside the agent's tree and its cgroup. It shows
only in the machine-wide numbers.

**Recommendation: A, alone, first.** It is the only one that is per command
and right for background jobs, it touches nothing the agent sees, and its
blind spot is commands under one tick, which are not the ones that exhaust a
machine. C is dropped: A covers it. **B is a later, optional PR**: it makes
the per-agent totals exact and lets `end_agent` kill what an agent left
behind with `cgroup.kill` in place of the orphan heuristic, and when an
agent's `memory.peak` rises while exactly one of its commands is open, that
command's row gets the exact figure. It is worth building only if the retro
shows sampled peaks misleading agents (question 5).

Mechanism for A, all in watchd's existing `machine_tick`: keep a table in
memory of live command shells per agent (pid, start, command text, largest
RSS sum, last CPU reading). When a shell is gone, write one history row if
it cost something: wall ≥ 60 s or peak ≥ 1 GiB. That threshold is on the
measurement, not on words, and only keeps `ls` out of the history. A watchd
restart loses the commands open at that moment.

### The history, and where each piece lives

One row per finished command:
`ts, machine, repo, agent, source, cmd, key, wall_s, cpu_s, peak_kb, exact`.

| Piece | Lives | Why |
|---|---|---|
| The store | outside `swarm.db`: one SQLite file per user and machine, `$XDG_STATE_HOME/cmd-cost/history.db`, schema documented in this repo | A cost belongs to a command on a machine, not to a swarm. It must outlive a swarm, span repos ("the most intensive commands in which repos") and accept writers that are not the swarm. |
| Measuring agents' commands | swarm (watchd, means A) | Only the swarm knows which process tree is which agent. About 40 lines in `machine_tick`. |
| `swarm run` jobs | swarm, same rows | It already records each job's RSS and CPU, here and on other machines. `machine` says where. |
| A repo's own build entry point (`nix run .#build`, a `just` recipe) | the repo, optional | It may wrap itself (`systemd-run --scope`, or `time -v`), which is exactly the per-command exactness the swarm can't have without rewriting commands. It writes rows with `source='repo'` and `exact=1`; predictions prefer them. The swarm ships the schema and a five-line shell example, nothing else. |
| CI | not a source for predictions | A CI runner is another machine, and its rows would only predict CI. A repo that wants them writes them with `machine='ci'`; the swarm neither reads nor needs them. |
| Reading | swarm: `swarm cost` | Small: one query. |

`swarm cost` (read-only, the whole agent-facing surface):

- `swarm cost "<words>"`: what a command is expected to take here: "`cargo
  test --release`, this repo, this machine: 5 runs, median 6 min, peak
  9.4G (max 11.2G), 31 CPU-min." Matched on `key`.
- `swarm cost --top [--repo R | --all-repos]`: the most intensive commands,
  by peak and by CPU time.

`key` is the command with a leading `cd … &&`, environment assignments and
trailing pipes and redirections stripped, cut to its first three words. That
is a shortcut to tune from real rows; the full `cmd` is kept so a better key
can be recomputed. Rows are pruned to the newest 20 per `(machine, repo,
key)`.

### What the agent sees, and when

No word decides anything, and nothing is printed for a command that is not
predicted to matter:

- **Before a Bash command**, the hook looks the key up (one indexed read).
  It adds context only when the history predicts a peak above half the
  memory available now, or pressure is high and the command has any history:
  "`cargo test --release` took ~9.4G and 6 min the last 5 times here; 6.1G
  is available now. Running: sr-4 5.1G (cargo), other sessions 8G." Context
  only, never a deny. A command with no history gets nothing, runs, and is
  measured.
- **The machine note** (`swarm machine`, and the commands below) lists
  memory per agent with its largest process, and "other sessions", by
  measured size. No pattern picks which processes count.
- **Where every role decides**, not only before a build:

| Decision | Command | Shows |
|---|---|---|
| What do I do next? | `swarm board` | the one-line `machine_line` first (as `who` has) |
| Do I take this now? | `swarm task claim` | the line; the full note when pressure is high |
| Do I add an agent? | `swarm spawn` | the full note, the live count and the count the user launched (§6) |
| What will this cost? | `swarm cost` | the history |

- **The `pressure` edge** goes to the agents holding the most memory (by
  measurement, top three) and to every stayer: the long-lived deciders,
  whatever they call themselves. One non-urgent notice per edge, so never a
  cold wake.

What else read the word list, and what it reads now: `oom_score_adj` 500
goes on every process in an agent's tree except its claude process; the
orphan kill takes any process reparented to init whose cwd is in an ended
agent's worktree; the panel's "heavy" card and `swarm-retro`'s
`heavy_starts` read history rows.

Off Linux there is no `/proc`: nothing is measured, the history stays empty
for that machine, and the note has only what `mem_psi` gives. That is today's
behaviour there.

### Auto-spawn's limits

They are two different things:

- `--min-free-mem` is not a gate on agents. watchd is a script, it can't
  weigh a machine note, and a threshold is its stand-in for judgment about
  its *own* spawns. It stays, for the scripted path only. Agents' spawns are
  never refused for memory; they get the note. What changes: today watchd
  skips the spawn silently (`watchd.lua:441`). It should log an edge-triggered
  `spawn-held` event with the reason, and the board should carry one line
  while it holds ("auto-spawn holding: 3.1G free, wants 4G; 2 tasks
  startable"), so whoever reads the board can decide: spawn anyway, pick a
  smaller task, use another machine. With an orchestrator and
  `--max-agents 0`, watchd decides nothing and both numbers are only
  information.
- `--max-agents` is the user's budget, not machine contention. For watchd it
  stays a limit. For agents it is information or a limit: question 1.

## 7. Deleted or simplified

- `is_comms`' name-suffix rule and the lifecycle exemption for the
  communicator (one general rule replaces a special case).
- `ctx_advice`'s communicator branch becomes the stayer branch.
- DESIGN's "no roles" wording in three places becomes one decision.
- The panel's "comms not counted, shown apart" explanation: it is a stayer
  with a role like any other; its own row can stay.

- The whole heavy-word system (§6a): `HEAVY_RE`, `NOT_HEAVY`, `is_heavy`,
  `.claude/swarm.json` `heavy`, `heavy-start`, `heavy-count`. With the
  optional cgroup PR, the orphan-kill heuristic too.

Not deleted, though tempting: `reusable`/`passed_over`/the digest. They are
about reusing small-context implementers, not about roles.

## 8. Migration: small PRs, each landable alone

Each passes `luajit swarm/lua/test/run.lua` and carries its own brief lines.

1. **`role`.** Column, `swarm role`, `spawn --role`, `who`/`board`/`state`/
   roster output, brief bullet (role half). No lifecycle change. *Tests:* set,
   change, print; event logged; a write from another terminal is fenced; the
   same-role line names the peer; role survives takeover.
2. **`stay`.** Column, `swarm stay [--end]`, `spawn --stay`, the lifecycle
   term and the `end_agent` re-check, `_release` clears it, `ctx_advice` and
   `task done` wording, brief bullet (stay half) and Ending line. *Tests:* an
   idle, claimless, landed agent with a stay is not ended and not digested;
   after `--end` it is; `stay` set between judgment and end keeps it; reap of
   a dead terminal clears it; takeover keeps it; a stayer's expired claim
   still reopens.
3. **Quiet notice (after 2).** *Tests:* one message per stayer and one
   notice to the communicator on the edge; none on the next tick; a new task
   re-arms it; a cold or waiterless stayer is named to the communicator, not
   woken.
4. **Communicator as stayer (after 2).** `watchd` sets it; delete the
   exemption and the suffix rule. Restart each live swarm's watchd on the new
   code before the deletion merges (its start sets the stay). *Tests:* the
   existing "communicator: never digested, never ended" tests pass unchanged;
   an agent merely named `x-comms` is no longer special.
5. **Panel (after 1, 2).** Role chip, "staying", the four event kinds.
6. **SKILL.md and DESIGN.md (after 1-4).** Decision 9, the two starts.
7. **Measure and record (independent).** Command shells in `machine_tick`,
   the history file and its schema doc, `swarm run` rows, `swarm cost`.
   Adds only; the word list still runs. *Tests* (fake `/proc`): a shell seen
   on three ticks then gone writes one row with the largest RSS sum, the
   last CPU reading and the command text; two concurrent shells of one agent
   write two rows; a short, small command writes none; `cost` prints the
   median and max; pruning keeps 20.
8. **Read measurements, delete the words (after 7).** The machine note,
   `pressure` recipients, `oom_score_adj`, the orphan kill, the panel card
   and `swarm-retro` read sizes and history rows; the pre-Bash prediction
   replaces the heavy trigger. Then `HEAVY_RE`, `NOT_HEAVY`, `is_heavy`, the
   `swarm.json` key and both events go, in the same PR, so nothing is left
   reading an event nobody writes. *Tests:* no context for a command without
   history; context when the predicted peak is above half of what is
   available; a process no word names is listed by size; the old heavy
   tests are deleted with the code.
9. **Telemetry at decisions (independent; `pressure` to stayers after 2).**
   The machine line on `board` and `task claim`, the note and counts on
   `spawn`, `spawn-held` and its board line. The spawn refusal only if the
   user says yes to question 1. *Tests:* each command prints the line from a
   fake `/proc`; one `spawn-held` per edge; no agent spawn is refused for
   memory.
10. **A cgroup per agent (optional, after 7; question 5).** `spawn` launches
    through `systemd-run --user --scope` where it exists; exact per-agent
    peak and CPU; `end_agent` uses `cgroup.kill`. Without systemd nothing
    changes.

After 2 lands the roles request is met for agents; 3-6 are nudges, cleanup
and views. 7-10 are the telemetry and stand apart from roles: they can go
first.

## 9. Considered and not proposed

- **A role as a lease-less "standing task"** (claimable, exclusive, on the
  board, re-staffed by auto-spawn when its holder dies). It reuses ownership,
  but it drags roles back into the task shape the request wants out of, and
  it touches the pool, auto-spawn, "all tasks done", task timing in the retro
  and the board model (#107). Revisit if runs show roles going unfilled after
  a holder dies.
- **Exclusive or enumerated roles**, `post @reviewer`, role-scoped task
  visibility (DESIGN phase 3). Each is the swarm imposing a flow.
- **Routing PR events to reviewers from watchd.** It needs subscriptions. A
  peer's one-line post to the reviewer, found on the board footer, costs one
  wake of one agent.
- **A timer on `stay`** (decision 7).
- **Hook timing, a cgroup per command, eBPF** as the way to measure (§6a).
- **Telling an agent what its command cost after it ran.** The next agent
  to run it is told before; a line after every build is prompt noise.

## 10. Risks, and questions for the user

Risks:

- **A label may change nothing** (finding 3). Expected: the label is for
  reading. If hard work goes unowned, the fix is structural, not a stronger
  role prompt.
- **Conformity.** Same-model agents may all declare the same role or none.
  Mitigation is only the same-role line and the roster. Measure in the retro
  from `role` events.
- **Stayers leak.** A forgotten stayer holds about 300 MB and is never ended.
  The quiet notice and the visible sentence are the only pressure.
- **A standing reviewer ages.** Principle 5 wants reviewers with a fresh
  context. A reviewer per PR as an ordinary task (auto-spawned, fresh, another
  model) is often better than a stayer, and already works. The brief should
  not push `stay`.
- **An orchestrator is the bottleneck DESIGN was written to avoid**, and its
  messages are peer data, not orders. It has real power only through the
  board and `spawn`. Two orchestrators have no arbiter but claims.
- **Spawn cost.** An orchestrator that spawns freely spends the user's quota.
- **The quiet notice wakes large contexts.** Bounded by the cold guard: cold
  stayers are reported, not woken.

- **Sampled peaks run low** (a spike between two 30 s samples), so a
  prediction can understate. The row says `exact=0`; `source='repo'` rows
  and PR 10 are the two ways to exact figures.
- **The command key is crude.** Three words can merge a one-crate test with
  a workspace test. The median hides that; the max shown beside it doesn't.
- **Daemon-side work** (`nix build`, `docker build`) is in no agent's tree
  and is never attributed.

Questions:

1. Should the user's agent count bind agents' own spawns? Recommended: yes,
   one number in `meta` that `swarm spawn` refuses past, naming the
   communicator as who can raise it. It is the user's budget, not contention
   between agents, so decision 6 doesn't cover it. The alternative is the
   information line alone.
2. Is PR 4 wanted now? It deletes a special case but touches the one agent
   whose wrongful end hurts most.
3. `stay` as the word (`hold` and `wait` are taken or confusable)?
4. Keep `--min-free-mem` as watchd's own threshold (recommended, made
   visible by `spawn-held`), or drop it and let auto-spawn launch whatever
   the cap allows, leaving memory to the agents' notes?
5. Build the per-agent cgroup (PR 10)? Recommended: not until a retro shows
   sampled peaks misleading agents. It is Linux-with-systemd only and
   changes how every agent is launched.
6. Should the user's own Claude Code sessions outside a swarm be measured
   too? Their builds are most of the load on a shared machine and today
   appear only as "other sessions". watchd could record any command shell
   under any claude process in the repo's worktrees; not planned unless
   wanted.

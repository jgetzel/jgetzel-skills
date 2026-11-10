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
when the swarm goes quiet, and checks them for hangs. Nothing in the CLI or watchd ever reads the text of
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

**Hung stayers** (the user's concern, 2026-11-09: a stayer can hang for
hours with nothing waking it). A sleeping stayer and a hung one look the
same until something tries to reach it, so watchd looks for the signs it can
see and, failing those, asks:

| Sign | Kind | What watchd does |
|---|---|---|
| Terminal gone | edge | `reap` ends it (today) |
| hc reports a prompt or any status but idle/working | edge | tells the communicator (today's blocked notice) |
| Idle with no live waiter: no message can wake it | edge | tells the communicator once: "sr-7 stays for '<text>' but has no waiter and can't be woken." A poke would not arrive. |
| A message to it is unread two ticks after it was posted, and it is still idle | edge | tells the communicator once: "sr-7 did not wake on a message." This fires exactly when someone needs the stayer. |
| None of the above, idle 50 min | **periodic** | the liveness check below |

The liveness check is a timer, against decision 7, because the user asked
for it and because no edge exists for "hung while nobody needs it yet". It
is the only one. After 50 minutes idle watchd posts to the stayer: "Liveness
check: you have stayed 50 min for '<text>'. If that still holds, do nothing.
If it is over, `swarm stay --end`." The answer is not a reply: the wake
itself moves the agent's `last_active`. If that hasn't moved five minutes
later, the stayer is hung: one urgent notice to the communicator with its
terminal and hc status ("unstick it with `hc send`, or end it"), event
`stay-hung`, and no more checks until it is active again. A stayer that
answers is checked again after another 50 idle minutes.

Why 50: the prompt cache lasts an hour (`COLD_IDLE` is 55 min). A check
inside that window is a short cached turn and renews the cache, so a stayer
is never a cold wake when it is finally needed. A check after it would
resend the whole context uncached each time. The cost is about a tenth of
the stayer's context per check, for as long as it stays; `who` shows how
long that has been. The user approved the repeating check (2026-11-09). The
communicator is not checked: it has no hooks, and the user is its liveness.

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
| Auto-spawn per task | watchd staffs every startable task | unchanged and optional: it is the scripted orchestrator. A swarm whose orchestrator staffs tasks itself sets the auto-spawn number to 0 (§6). Both can run: `spawn --task` reserves, so they can't double-staff. |
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
orchestrator possible. Two numbers, both the user's, bound how many agents
the swarm holds (the user, 2026-11-09):

| | Auto-spawn number (the user's "agent min") | Agent max |
|---|---|---|
| Means | watchd staffs startable tasks until this many agents are live | the most agents that may be live at once |
| Binds | watchd: it never spawns past it | **every spawn**: `swarm spawn` refuses at the max |
| Lives | `meta.agent_min` | `meta.agent_max` |
| Default | the live count when the first watchd starts (today's rule) | none: no max, and no refusal, until the communicator sets one |

Both count every live agent but the communicator, stayers included: each
holds memory and quota whatever it calls itself.

- **Who sets them:** the communicator, on the user's word, with
  `swarm limits [--min N] [--max M]`. With no flag it prints both and the
  live count. It refuses a min above the max. watchd reads `meta` each tick,
  so a change needs no restart. `watchd --max-agents N` remains for one
  release as a way to write the auto-spawn number at start, then goes.
- **The refusal is a deterministic check in `spawn`**, not a note. The count
  and the new agent's row are written in one transaction before the launch
  (sw-ownership rule 3), so two spawns at once can't both take the last
  place. Today a spawn without `--task` reserves nothing (`watchd.lua:718`);
  it must reserve its row like `--task` does. At the max: "12 agents are
  live and the user's max is 12. The communicator can raise it." Exit
  non-zero, event `spawn-refused` (the retro then shows unmet demand). It
  binds the communicator too: it raises the number first.
- **What agents see before they try:** `swarm board` and `swarm who` open
  with "agents: 9 live, auto-spawn to 8, max 12" (or "no max set").
- **SKILL.md's start step** tells the communicator to ask the user for both
  numbers and set them before the first spawn.
- **Below the auto-spawn number:** watchd staffs tasks, as today.
- **Between the two:** watchd spawns nothing. More agents come only from an
  agent that judges one is needed: an orchestrator staffing a plan, an
  implementer who wants a reviewer on another model.
- **Auto-spawn number 0:** watchd staffs nothing; an orchestrator does.
- A relaunch successor is not a spawn (it takes over a name), so it is
  never refused.

This is a gate, and decision 6 prefers information. It is recorded as the
user's budget, like `--max-agents` before it: a limit on spending, not a
way to settle contention between agents.

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
an auto-spawn number of 0. The communicator stays out of the event path either
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

**Recommendation: A for every command, B on top where it exists.** A is the
only one that is per command and right for background jobs, it touches
nothing the agent sees, and it is the only one that also works on macOS
(below). Its blind spot is commands under one tick, which are not the ones
that exhaust a machine. C is dropped: A covers it. B is built wherever a
systemd user session exists (the user, 2026-11-09): it makes the per-agent
totals exact, lets `end_agent` kill what an agent left behind with
`cgroup.kill` in place of the orphan heuristic, and when an agent's
`memory.peak` rises while exactly one of its commands is open, that
command's row gets the exact figure (`exact=1`). Nothing depends on B: with
no cgroup every number is A's.

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
| The user's own Claude Code sessions | swarm (watchd), same rows | The user, 2026-11-09. Their builds are much of the load and today show only as "other sessions". watchd records command shells under any claude process whose cwd is in this repo or one of its worktrees, with `agent` set to `user:<its -n name>` or `user`. **Measure only:** no `oom_score_adj`, no kill, no notice, nothing written anywhere but the history. The note lists them by name where it says "other sessions" today. |
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

### macOS, without sudo

A requirement from the user (2026-11-09): the tool must work on macOS with
no sudo. There is no `/proc`, PSI or cgroup there. Nothing below was run on
a Mac; the first job of the PR is to run it on one.

**One seam.** Everything that asks "what is running" or "how full is the
machine" goes through two functions in `machine.lua`, and nothing else reads
the system:

- `procs()`: one row per process: pid, ppid, RSS, elapsed time, CPU time,
  full arguments. One implementation for both systems:
  `ps -axww -o pid=,ppid=,rss=,etime=,time=,args=`, the column set procps
  and BSD `ps` share (checked on Linux here). It replaces the hand-written
  `/proc/<pid>/stat` scan and `claude_pid`'s walk, so the code a Mac runs is
  the code Linux tests. Cost: one `ps` per tick.
- `mem()`: memory available, total, and a pressure reading.

| Reading | Linux | macOS |
|---|---|---|
| Processes, trees, RSS, command text | `ps` | `ps` |
| CPU of a command | the shell's `cutime+cstime` from `/proc` (exact for reaped children); else as macOS | the sum of `time` over the tree's processes as last seen: a lower bound, since a child that exits between ticks is missed |
| Memory available, total | `/proc/meminfo` | `sysctl -n hw.memsize`; `vm_stat` free + inactive + speculative + purgeable pages |
| Pressure | PSI `some avg10` | `sysctl -n kern.memorystatus_vm_pressure_level` (normal, warn, critical); load from `sysctl -n vm.loadavg` against `hw.ncpu`. "High" is warn or worse. |
| A process's cwd | `/proc/<pid>/cwd` | `lsof -a -d cwd -Fpn` once per tick (own processes need no sudo) |
| Exact per-agent peak and CPU | cgroup, with systemd | none; rows stay `exact=0` |

So on a Mac the history, `swarm cost`, the prediction and the machine note
all work, with sampled memory and a low CPU figure. Wall time and memory
are what the prediction leans on.

**What else assumes Linux today**

| Where | Assumes | On macOS |
|---|---|---|
| `machine.mem_psi`, `machine_line` | `/proc/meminfo`, `/proc/pressure`; prints "unknown (no /proc here)" | `mem()` above |
| `machine.read_procs`, `claude_pid`, `heavy_procs`, `bg_agents` | `/proc/<pid>/stat`, `cmdline`, `comm` | `procs()`. `bg_agents` matters most: without it an idle owner's background job is invisible and `reap` takes its claim. |
| `watchd.mem_available_gib` (`--min-free-mem`) | `/proc/meminfo`; without it returns infinity, so the threshold never holds | `mem()` |
| `sweep_worktrees` | `/proc/<pid>/cwd`; without `/proc` it sweeps nothing | `lsof`; if that fails, still sweep nothing (never guess a tree is unused) |
| Orphan kill in `machine_tick` | `/proc/<pid>/cwd`, ppid 1 | `procs()` and `lsof`; with a cgroup on Linux, `cgroup.kill` |
| `oom_score_adj` 500 on agents' processes | Linux OOM killer | nothing, and no substitute: macOS has no per-process knob an unprivileged user can set. It compresses and swaps instead of killing. Skipped silently. |
| `run.lua` `PROBE` for other machines | `nproc`, `/proc/loadavg`, `/proc/meminfo`, `/proc/pressure` on the far side | the far side runs `swarm machine --json` if it has swarm, else a `uname` branch with the `sysctl` and `vm_stat` calls above |
| `agents.herdr_stale` | `sha256sum` | `shasum -a 256` when `sha256sum` is absent |
| Per-agent cgroup (new) | systemd user session | absent; launch unwrapped |
| The history path | `$XDG_STATE_HOME`, default `~/.local/state` | the same path; it is only a directory |
| Tests | a fake `/proc` tree (`SWARM_PROC`) | fixtures become canned `ps`, `vm_stat` and `sysctl` output through the seam, so both systems' parsing is tested on either |
| `hc`, Herdr, `launch.sh` | not Linux as such, but every spawn, liveness check and kill goes through `hc` | not examined: whether `hc` and the Herdr app run on macOS decides whether there is a swarm there at all. The open question in §10. |

Already portable: SQLite, LuaJIT and the rocks (`install.sh` has a Homebrew
route), `git`, `gh`, `du -sk`, the `swarm` shell wrapper, signals.

### Auto-spawn's limits

Three numbers, and none of them refuses an agent anything:

- **`--min-free-mem`** stays (the user, 2026-11-09). watchd is a script, it
  can't weigh a machine note, and a threshold is its stand-in for judgment
  about its *own* spawns. Agents' spawns are never held for memory; they get
  the note.
- **The auto-spawn number** (§6) is the other bound on watchd's own spawns.
- **The agent max** (§6) is information to agents.

What changes for watchd: today it skips a spawn silently
(`watchd.lua:441`). It logs an edge-triggered `spawn-held` event with the
reason, and the board carries one line while it holds: "auto-spawn holding:
3.1G free, wants 4G; 2 tasks startable", or "auto-spawn holding: 8 live, the
auto-spawn number is 8; 2 tasks startable; max 12". Whoever reads the board
can then decide: spawn anyway, pick a smaller task, use another machine.

## 7. Deleted or simplified

- `is_comms`' name-suffix rule and the lifecycle exemption for the
  communicator (one general rule replaces a special case).
- `ctx_advice`'s communicator branch becomes the stayer branch.
- DESIGN's "no roles" wording in three places becomes one decision.
- The panel's "comms not counted, shown apart" explanation: it is a stayer
  with a role like any other; its own row can stay.

- The whole heavy-word system (§6a): `HEAVY_RE`, `NOT_HEAVY`, `is_heavy`,
  `.claude/swarm.json` `heavy`, `heavy-start`, `heavy-count`. With the
  cgroup PR, the orphan-kill heuristic on Linux too.
- The hand-written `/proc/<pid>/stat` scanner (`read_procs`, `claude_pid`):
  `ps` does it on both systems.
- `watchd --max-agents`, after one release.

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
   (The start step's "ask the user for both numbers" lands with 12.)
7. **The seam, and macOS (independent; first of the telemetry).** `procs()`
   on `ps` and `mem()` per system; `read_procs`, `claude_pid`, `mem_psi`,
   `mem_available_gib`, the cwd reads, `PROBE` and `herdr_stale` go through
   them or get their macOS branch; `oom_score_adj` is skipped off Linux. No
   behaviour change on Linux. *Tests:* canned `ps` output from both systems
   parses to the same rows; canned `vm_stat` and `sysctl` give available
   memory and a pressure level; the existing machine, reap and sweep tests
   pass on the new fixtures. *Done also needs:* the suite and one live
   two-agent swarm run on a Mac, with no sudo.
8. **Measure and record (after 7).** Command shells in `machine_tick`, the
   history file and its schema doc, `swarm run` rows, `swarm cost`. Adds
   only; the word list still runs. *Tests:* a shell seen on three ticks
   then gone writes one row with the largest RSS sum, the last CPU reading
   and the command text; two concurrent shells of one agent write two rows;
   a short, small command writes none; `cost` prints the median and max;
   pruning keeps 20; a shell under a non-swarm claude process in a worktree
   writes a `user:` row, and one outside the repo writes none; no code path
   signals or writes `oom_score_adj` for a process outside an agent's tree.
9. **Read measurements, delete the words (after 8).** The machine note,
   `pressure` recipients, `oom_score_adj`, the orphan kill, the panel card
   and `swarm-retro` read sizes and history rows; the pre-Bash prediction
   replaces the heavy trigger. Then `HEAVY_RE`, `NOT_HEAVY`, `is_heavy`, the
   `swarm.json` key and both events go, in the same PR, so nothing is left
   reading an event nobody writes. *Tests:* no context for a command without
   history; context when the predicted peak is above half of what is
   available; a process no word names is listed by size; the old heavy
   tests are deleted with the code.
10. **Telemetry at decisions (after 7; `pressure` to stayers after 2).**
    The machine line on `board` and `task claim`, the note on `spawn`.
    *Tests:* each command prints the line from the fixtures.
11. **A cgroup per agent (after 8).** Where a systemd user session exists,
    `spawn` launches through `systemd-run --user --scope`; exact per-agent
    peak and CPU; the exact figure on a command's row when it was the only
    one open; `end_agent` uses `cgroup.kill`. Elsewhere the launch is
    unwrapped and nothing changes. *Tests:* with a fake cgroup directory a
    lone command's row is `exact=1` with `memory.peak`; with two open it
    stays sampled; with no `systemd-run` on PATH the launch line is today's.
12. **The two numbers (independent).** `meta.agent_min` and `agent_max`,
    `swarm limits`, watchd reading them each tick, every spawn reserving its
    row before launch, the refusal at the max, the line on `board` and
    `who`, `spawn-held` and its board line. *Tests:* watchd spawns up to the
    auto-spawn number and not past it; a change takes effect on the next
    tick; a spawn at the max is refused, launches nothing, leaves no row and
    logs `spawn-refused`; two spawns racing for the last place: one wins;
    raising the max lets the next through; with no max set nothing is
    refused; `limits` refuses a min above the max; one `spawn-held` per edge.
13. **Hung stayers (after 2).** The two edge notices and the liveness check.
    *Tests:* a waiterless idle stayer is reported once; an unread message
    two ticks old is reported once; a check goes out at 50 idle minutes and
    not before; a moved `last_active` means no `stay-hung` and a new check
    50 minutes later; an unmoved one means one `stay-hung` and no further
    checks; the communicator is never checked.

After 2 lands the roles request is met for agents; 3-6 and 13 are nudges,
cleanup and views; 12 is the staffing numbers. 7-11 are the telemetry and
stand apart from roles: they can go first.

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
  The quiet notice, the liveness check's question and the visible sentence
  are the only pressure.
- **A standing reviewer ages.** Principle 5 wants reviewers with a fresh
  context. A reviewer per PR as an ordinary task (auto-spawned, fresh, another
  model) is often better than a stayer, and already works. The brief should
  not push `stay`.
- **An orchestrator is the bottleneck DESIGN was written to avoid**, and its
  messages are peer data, not orders. It has real power only through the
  board and `spawn`. Two orchestrators have no arbiter but claims.
- **The max is a gate.** An orchestrator at the max can't staff its plan
  and can only ask the communicator, which waits on the user. That is the
  point of a budget, and it is also the manager-attention bottleneck in a
  new place. `spawn-refused` events show how often it bites.
- **The liveness check costs tokens for as long as an agent stays**, about
  a tenth of its context every 50 minutes, and it is a timer.
- **The quiet notice wakes large contexts.** Bounded by the cold guard: cold
  stayers are reported, not woken.

- **Sampled peaks run low** (a spike between two 30 s samples), so a
  prediction can understate. The row says `exact=0`; `source='repo'` rows
  and the cgroup (PR 11) are the two ways to exact figures.
- **The command key is crude.** Three words can merge a one-crate test with
  a workspace test. The median hides that; the max shown beside it doesn't.
- **macOS is planned from documentation, not run.** The `ps` columns,
  `vm_stat` arithmetic and the pressure sysctl need a Mac before PR 7 is
  done. CPU figures there are lower bounds.
- **Daemon-side work** (`nix build`, `docker build`) is in no agent's tree
  and is never attributed.

Answered by the user, 2026-11-09 (relayed by the communicator):

- Two numbers: watchd's auto-spawn number, and an agent max at which
  `swarm spawn` refuses (§6).
- `stay` is the word. Stayers are checked for hangs, with the repeating
  50-minute liveness check (§4).
- `--min-free-mem` stays as watchd's own threshold, made visible (§6a).
- PR 4, the communicator as a stayer: wanted.
- The per-agent cgroup: build it where systemd user sessions exist.
- The tool must work on macOS without sudo (§6a, PR 7).
- The user's own sessions in this repo are measured, and only measured
  (§6a).
- The agent max has no default: none until the communicator sets one (§6).

Open, found while planning macOS and not yet put to the user:

1. Do `hc` and the Herdr app run on macOS? If not, macOS support needs a
   second way to launch, watch and end an agent's terminal, which is a
   larger piece than anything in PR 7 and is not planned here.

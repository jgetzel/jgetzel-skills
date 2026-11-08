# sw-substrate: what /swarm can be built on, in this environment

Lane `sw-substrate`, research wave for `/swarm`, 2026-11-07. Environment:
Claude Code 2.1.316, hc (herdr-core) 0.1.16, herdr-app 0.1.11, NixOS, 12 cores,
31 GiB RAM. Local measurements are marked **(measured)**. Claims about Claude
Code come from the official docs at code.claude.com and are cited. Anything I
couldn't verify is marked **unverified**.

## TL;DR

- **Cross-session `SendMessage` is the best wake and DM primitive available,
  and it's already in use here.** Delivery is local and goes over a per-session Unix
  socket. A busy receiver reads the message between tool calls. An idle
  receiver gets a new turn started for it. The receiver is told the message
  came from another session, not from the user. The harness also throttles
  loops: it drops identical repeats, rate-limits per sender, caps the queue at
  50 and refuses bursts at the sender
  ([docs](https://code.claude.com/docs/en/cross-session-messaging)). I saw
  this happen in this session: two peer pointers arrived as system reminders
  between my tool calls, mid-turn.
- **It is not a channel system.** There is no broadcast, no rooms, no history,
  and no record the human can read in one place. A delivered message also
  wakes the receiver with its whole context. The docs say a message to an idle
  session "start[s] a new turn … sending your full context each time"
  ([costs](https://code.claude.com/docs/en/costs#why-usage-climbs-in-a-long-session)).
  At swarm scale, **the cost of a message is the receiver's context size, not
  the message's size.**
- **Mode mismatch silently breaks delivery.** Suppose some sessions run in
  `bypassPermissions` and others prompt (auto, acceptEdits, dontAsk). Then
  messages across the two groups are *held* for human approval, and dropped
  after `dialogExpiry` (5 min). Every swarm agent must run in the same
  permission-mode class, or set `crossSessionInbound: accept` explicitly.
- **Agent teams don't fit a flat swarm of dozens.** A team has one fixed lead
  and one team per session. Teams can't nest. In-process teammates die with
  the lead. Split panes need tmux or iTerm2, and Herdr is neither. Teammates'
  permission prompts all go to the lead. Plan-mode teams use about 7× the
  tokens ([agent teams](https://code.claude.com/docs/en/agent-teams#limitations),
  [costs](https://code.claude.com/docs/en/costs#manage-agent-team-costs)). Its
  primitives are still worth copying: a JSON mailbox per agent, a task list
  claimed under a file lock, and the `TeammateIdle`/`TaskCompleted` gates.
- **`hc send` is for launching and unsticking agents, not for messaging.** It
  pastes into the receiver's input box as if the user had typed it. That means
  no peer provenance (the model sees it as user input) and collisions with a
  human typing there. A send to a booting agent can also be dropped
  ([hc skill](../../hc/SKILL.md)). Gas Town's tmux "nudge" has the same shape
  ([gastown](https://github.com/steveyegge/gastown)).
- **Hooks can make rooms and channels feel native without asking the model
  for discipline.** `PostToolUse`/`PostToolBatch` can inject unread room
  traffic as `additionalContext` at the next tool round. An `asyncRewake`
  background hook "wakes Claude immediately even when the session is idle"
  when it exits 2 ([hooks](https://code.claude.com/docs/en/hooks#run-hooks-in-the-background)).
  A `PostToolUse` hook on `SendMessage` can mirror every DM into a shared log
  the human can watch. A `PreToolUse` hook can enforce message budgets.
- **MCP channels are the "real" push bus, but still a research preview.** A
  stdio MCP server that declares `claude/channel` can push `<channel>` events
  into a running session
  ([channels reference](https://code.claude.com/docs/en/channels-reference)).
  Custom channels need `--dangerously-load-development-channels`, which shows
  a confirmation dialog on every launch, and a v2-runtime handshake caveat
  applies. Use it for v2, not v1.
- **Capacity (measured):** each `claude` process holds 226–323 MB of private
  dirty memory and about 25 threads. A working session uses 1–8% of one core;
  an idle one, about 0.6%. Fifty sessions come to roughly 15 GB for Claude
  alone, which fits here. The real limits are the processes agents spawn
  (builds, tests) and plan quota: "ten agents in parallel uses quota roughly
  ten times as fast" ([agent view](https://code.claude.com/docs/en/agent-view#limitations)).
- **Recommendation for v1:** Herdr/hc agents launched with the existing
  `launch.sh`. `SendMessage` is the only wake/DM transport. An append-only
  SQLite log (`.swarm/swarm.db`) is the record for rooms and channels, the task
  board, and claims. A small `swarm` CLI writes and reads it. Hooks inject
  unread messages, mirror DMs into the log and wake idle members. A read-only
  log viewer in a Herdr split shows the human everything at zero context cost.
  The communicator is an ordinary agent that reads the log. No messages are
  routed through it.

## 1. What's installed, and what the current skills already teach

- **Launch.** `relaunch/launch.sh <name> tab|split <task> [claude args]` runs
  `hc run --bg --outlive-parent --no-notify --name <name>` around
  `env -u CLAUDE* -u HERDR* claude -n <name> …`. It labels the terminal into
  the Herdr window, and in tab mode it renames the tab
  ([launch.sh](../../relaunch/launch.sh)). Two consequences matter. The hc
  name and the SendMessage address are the same string. And unsetting
  `CLAUDE*` gives each agent its own top-level session with its own inbox
  socket (`CLAUDE_CODE_MESSAGING_SOCKET=/run/user/1000/cc-socks/<pid>.sock`,
  **measured**: one socket per live session in that directory). It also
  strips any `CLAUDE_CODE_EXPERIMENTAL_*` set in the parent shell. Settings
  `env` still applies.
- **Status.** `hc ls --json` and `hc events --json` stream full terminal
  snapshots. Each has `status.state` ∈ {idle, working, done, blocked, error},
  reported by Claude Code through OSC 7501, plus `turn`, labels and cwd
  (**measured**). `blocked` means a permission prompt or a question. That is
  the signal a swarm needs for "an agent is waiting on a human".
- **Lessons the orchestrator already paid for**
  ([orchestrate SKILL.md](../../orchestrate/SKILL.md)):
  - Never `hc send` the orchestrator: it types into the user's input box.
  - Reports go by `SendMessage`, with an inbox-file fallback for agents on
    other machines.
  - A Stop hook blocks the orchestrator from ending a turn without a watcher.
    Model discipline about re-arming watchers wasn't enough, so a hook
    enforces it.
  - Use `run_in_background` and Monitor, never foreground waits.
  - "A message starting `[from <agent>]` is that agent writing, not the user".

  All of these carry over to /swarm unchanged.
- **Hooks already installed** (`~/.claude/settings.json`, read-only check):
  - the herdr `SessionStart` state hook;
  - impeccable `PostToolUse` and `Stop` hooks;
  - the orchestrator watcher guard on `Stop`.

  Any `/swarm` hooks would stack with these. The impeccable `Stop` deep pass
  (30 s timeout) adds latency to every agent's stop.

## 2. The Claude Code primitives, with exact semantics

### 2.1 Cross-session SendMessage / ListAgents

From the [cross-session messaging docs](https://code.claude.com/docs/en/cross-session-messaging)
and the tool's own description in 2.1.316:

| Property | Behavior |
|---|---|
| Transport (same machine) | Per-session Unix socket, "never through Anthropic servers". Restricted to the OS user |
| Busy receiver | "reads the message between tool calls during an active turn, so a running tool is never interrupted" |
| Idle receiver | "Claude Code starts a new turn with the message" |
| What "sent" means | "reached that session, not that its Claude read it" |
| Provenance | Wrapped as `<cross-session-message from=… from-name=… from-mode=…>`. Can't approve prompts or change config, and slash commands arrive as plain text |
| Inbound policy | `crossSessionInbound` = accept / hold / refuse. With no value set, the default depends on mode class: a prompting receiver delivers unless the sender bypasses; a bypassing receiver holds unless the sender also bypasses |
| Holds | Dialog in interactive sessions. Dropped after `dialogExpiry` (default 5 min). At most 100 held, oldest dropped. `-p` sessions keep held messages until the deadline |
| Throttles | Size cap of about 1M characters. Burst refusal at the sender ("batch the rest into one message or wait"). Per-sender rate limit, identical repeats dropped "within a short window", at most 50 accepted messages queued, so "a message loop … stops on its own" |
| Idle notices | `notify_when_idle` (main conversation only, same machine): one notice per subscription, which expires after 12 h. A pure subscription "costs that session nothing" |
| Fan-out | None. One send per recipient |
| Discovery | `ListAgents` / `/list-agents` lists live local sessions that bound a socket. A bare name delivers when unique, otherwise use `name [ref]`. `claude agents --json` lists active sessions for scripts ([agent view](https://code.claude.com/docs/en/agent-view)) |
| Scripts posting | A hook or Bash child can post to its *own* session's socket (`CLAUDE_CODE_MESSAGING_SOCKET`, optional `{"type":"auth","token":…}` first line, 30 s line deadline). The message payload format is **not documented**, so posting from a script is **unverified** |
| Cost | A delivered message "counts toward usage like a prompt you type". An idle wake resends full context ([costs](https://code.claude.com/docs/en/costs#why-usage-climbs-in-a-long-session)) |

Gaps for a swarm:

- **Survival.** I found nothing on whether a queued message survives the
  receiver's process exiting before it drains. Assume it doesn't
  (**unverified**).
- **Auto-mode classifier.** The docs say auto mode's classifier "reviews each
  message before Claude Code delivers it" for *agent-team* messages
  ([agent teams](https://code.claude.com/docs/en/agent-teams#messages-between-agents)).
  Whether it also screens cross-session messages is **unverified**. If it
  does, a blocked message "never reaches the recipient".
- **Subagents.** A subagent's cross-session send "goes out under your parent
  session's address", and replies go to the parent. A lane's own subagents
  therefore can't hold their own cross-session conversations.

### 2.2 Agent teams

From [agent teams](https://code.claude.com/docs/en/agent-teams):

- **Enabling.** Experimental, behind `CLAUDE_CODE_EXPERIMENTAL_AGENT_TEAMS=1`.
  Interactive sessions only.
- **Mailbox.** `~/.claude/teams/{team}/inboxes/{agent}.json`. A message counts
  as sent only once the file write succeeds. Delivery is automatic, and the
  lead gets an idle notification that carries the teammate's final answer.
- **Task list.** `~/.claude/tasks/{team}/`. Tasks are pending, in progress or
  completed, and can have dependencies. Claims take a file lock. Teammates
  self-claim the next unblocked task.
- **Limits.**
  - One team per session.
  - No nested teams: "teammates cannot spawn their own teammates".
  - The lead is fixed.
  - In-process teammates can't run background subagents.
  - `/resume` doesn't restore in-process teammates.
  - Task status "can lag".
- **Permissions.** No per-teammate permission modes at spawn. Teammate
  prompts "appear in the lead session".
- **Cost and size.** "Start with 3-5 teammates." About 7× tokens in plan mode
  ([costs](https://code.claude.com/docs/en/costs#manage-agent-team-costs)).
  In-process teammates' prompt cache lasts 5 min by default.
- **Display.** Split panes need tmux or iTerm2. In-process teammates live
  inside the lead's TUI, so the human can't see them as Herdr tabs.

The fit for /swarm is poor, for structural reasons: the lead is a
coordinator by construction, which is the bottleneck /swarm is trying to
remove. A swarm agent *could* lead a 2–4-person team as a temporary pod for
one task, a "hierarchical-on-demand" pattern. That's an experiment, not a
substrate.

### 2.3 Hooks that matter

From [hooks](https://code.claude.com/docs/en/hooks):

- **Injection points.**
  - `additionalContext` arrives as a system reminder on the next model request.
  - `SessionStart` injects context at the start, and can set `watchPaths`.
  - `UserPromptSubmit` injects context next to a prompt. It also fires when a
    cross-session message or a `/loop` tick starts a turn.
  - `PostToolUse` injects context next to a tool result.
  - `Stop` and `SubagentStop` can block stopping (exit 2 or
    `decision: block`) and add context.
- **Background hooks.** `async: true` hooks deliver output "on the next
  conversation turn. If the session is idle, the response waits until the next
  user interaction. Exception: an `asyncRewake` hook that exits with code 2
  wakes Claude immediately even when the session is idle." Timeouts are still
  enforced for `asyncRewake`. I didn't find the maximum timeout or what
  happens when one runs out (**unverified**, needs a probe).
- **`FileChanged`** runs on a filesystem watch, but it "ha[s] no decision
  control". It returns only `watchPaths` and a `systemMessage` the user sees,
  so it **can't** wake or inform the model.
- **`TeammateIdle` and `TaskCompleted`**: exit 2 keeps a teammate working or
  refuses the completion. These are team-only.

### 2.4 Monitor and background tasks

The Monitor tool, as described in 2.1.316, streams each stdout line of a
background script into the chat as an event. Monitors expire after at most
30 min, and the agent has to re-arm them. `run_in_background` Bash
re-invokes the agent when the command exits. Both work as wake sources. The
cost is model discipline: the agent must re-arm after every expiry, and each
expiry is a turn with its whole context. The orchestrator needed a Stop-hook
guard for exactly this.

### 2.5 MCP, and MCP channels

- **Plain MCP servers are pull-only.** "Claude queries it during a task;
  nothing is pushed to the session"
  ([channels](https://code.claude.com/docs/en/channels#how-channels-compare)).
- **Context cost.** Tool definitions are deferred behind tool search, so a
  bus server costs only its names and instructions in context until used
  ([costs](https://code.claude.com/docs/en/costs#reduce-mcp-server-overhead)).
- **Channels push.** A server that declares
  `capabilities.experimental['claude/channel']` emits
  `notifications/claude/channel {content, meta}`. The model sees
  `<channel source=… k=v>body</channel>`.
  - Events "queue into the session and are processed in order". Several that
    arrive while busy are delivered together on the next turn.
  - The webhook walkthrough shows an idle session starting work on an event.
  - There are no acknowledgments. Events to a session that didn't register
    the channel are dropped silently.
  - Optional permission relay forwards tool-approval prompts out through the
    channel.
- **Channel limits**
  ([channels](https://code.claude.com/docs/en/channels#research-preview),
  [channels reference](https://code.claude.com/docs/en/channels-reference#test-during-the-research-preview),
  [mcp](https://code.claude.com/docs/en/mcp)):
  - Research preview.
  - Custom servers need `--dangerously-load-development-channels server:<name>`,
    which shows a full-screen confirmation in interactive sessions and is
    ignored in `-p`.
  - Auth must be claude.ai or a Console key.
  - On the v2 MCP runtime, a server that negotiates revision 2026-07-28 isn't
    registered as a channel. `MCP_PROTOCOL_NEGOTIATION=legacy` works around it.
  - The docs describe channels as stdio subprocesses, so each session gets
    its own server process. A shared bus needs a per-session shim talking to
    one daemon or database.

### 2.6 Background sessions and headless mode

- **`claude --bg`** sessions run under a supervisor. They're listed by
  `claude agents --json`, are messageable, and are stopped after about an
  hour idle and unattached, unless pinned. The next reply resumes them
  ([agent view](https://code.claude.com/docs/en/agent-view)).
- **`claude -p`** binds an inbox socket, so a long-running `-p` worker is
  messageable. Held messages there can't be approved, so start it with
  `crossSessionInbound: accept` in `--settings`. `--bare` binds no socket
  ([cross-session](https://code.claude.com/docs/en/cross-session-messaging#non-interactive-sessions)).
- **Fit.** Both lose the user's stated preference for agents they can watch
  and type into in Herdr tabs. They're useful as cheap, invisible workers, not
  as swarm members.

## 3. Candidate substrates compared

Context cost per message ≈ message tokens + (receiver idle ? a full-context
re-read at cache price : 0).

| Substrate | Latency, guarantee | Idle wake | Context cost | Scale on this box | Human observability | Main failure modes |
|---|---|---|---|---|---|---|
| **Pure SendMessage** | Sub-second to next tool round. At-most-once: "reached session", queue cap 50, dedupe, burst refusal | Built in | Message, plus a full-context wake when idle. N sends for N recipients | Dozens (socket per session) | Poor: scattered across transcripts, one-line previews | Mode-class holds expiring in 5 min. Lost if the receiver exits (**unverified**). Fan-out costs the sender N tool calls |
| **Agent teams** | Mailbox file write. Automatic delivery, idle notices to the lead | Built in | Same, plus about 7× in plan mode | 3–5 recommended; one lead | In the lead's TUI only (no Herdr tabs) | Lead bottleneck, no nesting, teammates die with the lead, status lag, prompts pile onto the lead |
| **File/SQLite bus + Monitor** | Poll interval (0.5–1 s locally). Durable log, at-least-once if readers track a cursor | Monitor event (re-arm every ≤30 min) | Only what the filter emits. Expiry wakes cost about 2 turns/h per agent | Dozens. SQLite WAL handles this write rate easily | Excellent: `tail`/viewer in a split | Agents forget to re-arm. Noisy filters get the monitor auto-stopped |
| **File/SQLite bus + hooks** | Next tool round (PostToolUse). Durable | `asyncRewake` waiter, or a SendMessage nudge | Only unread items, injected once | Dozens | Excellent | asyncRewake timeout semantics unverified. Hook stacking adds latency |
| **Small MCP server (tools only)** | Pull: agents must call `read` | None | Small (deferred tools) | Dozens, one process per session unless HTTP | Good if it logs | Agents forget to poll |
| **MCP channel server** | Push, in order, no ack | Built in (event starts a turn) | `<channel>` body per event | Dozens, one shim each | Good if it logs | Research preview, dev-flag dialog every launch, silent drops if not registered, v2 handshake caveat |
| **hc send** | Types after the "person pauses". Refused while `blocked` | Yes (it's a prompt) | Prompt-sized; a wake if idle | Dozens | Visible in the pane | Arrives as *user* input (trust laundering), collides with human typing, dropped while booting |
| **git / issues blackboard** | Seconds to minutes (fetch/poll). Durable, auditable | None (needs a poller) | Pull-sized | GitHub's REST API allows 5,000 req/h per user. 50 agents polling once a minute is 3,000/h | Excellent (PRs, issues) | Rate limits, merge noise, slow. Good for *work items*, bad for chat. Prior art: [beads](https://github.com/steveyegge/beads), [mcp_agent_mail](https://github.com/Dicklesworthstone/mcp_agent_mail) (HTTP MCP, SQLite + git, advisory file leases) |

Notes on the table:

- **Lost messages.** SendMessage refusals reach the sender as an error or a
  `[Cross-session delivery notice]`, but a held message that expires reports
  only "to a sender it can reach". A durable log underneath makes losses
  recoverable: the receiver reads unread items whenever it next runs.
- **Typing into input boxes.** Only `hc send` and `hc keys` do this. Keep them
  to launching agents, trust dialogs and an unresponsive agent, as
  orchestrate already does.
- **Permission prompts.** Any substrate stalls an agent stuck on a prompt.
  hc reports it as `blocked`, and its queued SendMessages wait. The
  communicator should watch `hc events` for `blocked` and tell the human. A
  peer must never "approve" anything; the harness enforces that
  ([cross-session](https://code.claude.com/docs/en/cross-session-messaging#how-a-session-treats-an-incoming-message)).

## 4. Capacity on this machine (measured 2026-11-07, 15:56)

Sampled with `/proc/<pid>/smaps_rollup` and two `top` samples 5 s apart, over
8 live `claude` processes. Five were working, including this lane's four
peers; one had been idle for 72 h.

| Metric | Range |
|---|---|
| RSS | 307–428 MB |
| PSS | 266–352 MB |
| Private dirty | 226–323 MB |
| Threads | 23–27 |
| CPU, working sessions (5 s sample) | 1.0–7.6% of one core |
| CPU, 72-hour-idle orchestrator | 0.6% |
| Host | 12 cores, 31 GiB RAM, about 24 GiB available, load 1.3 |

Implications:

- **RAM.** 50 sessions × about 300 MB ≈ 15 GB. That fits, but leaves about
  9 GB for everything the agents run. On this box (nix builds, cabal, web
  dev servers, e2e browsers), those children are the binding constraint, not
  the Claude processes. Each stdio MCP server or channel shim adds a process
  per session. A Bun or Node shim is roughly 30–60 MB (**unverified**, not
  measured).
- **CPU.** Claude itself is cheap: 50 agents × about 5% ≈ 2.5 cores. Builds
  and tests dominate. Swarm agents need a shared semaphore for heavy jobs, like
  linn-studio's `.claude/orchestrator/bin/heavy.sh` mentioned in the settings.
- **Quota.** Quota scales linearly with agents working at once
  ([agent view](https://code.claude.com/docs/en/agent-view#limitations)). Idle
  agents cost nothing until woken. So "dozens of agents" should mean dozens
  *registered* and perhaps 8–15 *working* at once, with parked agents woken
  by messages. API-key organizations face TPM/RPM limits, and the docs'
  per-user recommendations assume humans, not 50 concurrent loops
  ([costs](https://code.claude.com/docs/en/costs#rate-limit-recommendations)).
  How many concurrent Opus sessions a Max plan sustains is **unverified**.
- **Wake cost.** At a context of about 150k tokens, every DM to an idle agent
  costs about 150k cached-input tokens. Chatter between big-context agents is
  the swarm's main cost driver. Batch messages, and treat a wake as
  expensive.

## 5. Implications for /swarm

### v1 recommendation: "SendMessage for wakes, a SQLite log as the record, hooks for delivery"

Judgment call, made in away mode: this needs the least new machinery and
keeps every agent visible in Herdr. It reuses `launch.sh`, the hc status
stream and the orchestrator's lessons. Each piece can be swapped out later:
the log can sit behind a channel server in v2.

**Moving parts:**

1. **Launch.** Reuse `launch.sh <prefix>-<name> tab …`, with:
   - `--permission-mode auto` for every agent (one mode class);
   - `--settings '{"crossSessionInbound":"accept"}'` so holds can never
     strand messages;
   - an explicit `--model` per kind of work, as in orchestrate.

   Each agent gets `SWARM_NAME` and `SWARM_DB` through the brief. Hooks read
   `HC_TERMINAL_ID`, or the name from `hc get`.
2. **`.swarm/swarm.db`** (SQLite WAL, gitignored, at an absolute path shared by
   all worktrees). Tables:
   - `msg(id, ts, from, to_kind{dm,room,list}, to, body, thread)`;
   - `member(agent, room)`;
   - `cursor(agent, last_id)`;
   - `task(id, title, state, owner, needs, lease_until)`;
   - `claim(path_glob, agent, lease_until)`.

   This follows teams' file-locked claims and mcp_agent_mail's advisory
   leases.
3. **`swarm` CLI** (python3 stdlib, no dependencies): `join/leave <room>`,
   `post <room|@list> <text>`, `read [--unread]`, `who [room]`, `task
   add/claim/done`, `claim <glob>`. Agents call it through Bash. That costs no
   MCP context and one tool call per post, whatever the fan-out.
4. **Delivery hooks** (project `.claude/settings.json`, active only when
   `SWARM_DB` is set):
   - `PostToolBatch` or `PostToolUse` runs `swarm unread --me $SWARM_NAME
     --mark` and emits a compact digest as `additionalContext`. Working agents
     see room traffic at the next tool round, the same latency as SendMessage.
   - A `Stop` hook with `asyncRewake: true` runs `swarm wait --me
     $SWARM_NAME`. That blocks until a message arrives for one of the agent's
     rooms or DMs, then exits 2 with the digest, which wakes the idle agent.
     **Probe first:** maximum timeout, and behavior when it expires. If the
     timeout can't be long, fall back: `swarm post` prints which members are
     idle (from `hc ls`), and the poster sends each one a one-line SendMessage
     nudge ("new in #room").
   - A `PostToolUse` hook on `SendMessage` appends `{from, to, message}` to
     `msg`, so DMs show up in the human's view too, with nothing the agents
     have to remember.
   - A `PreToolUse` hook on `SendMessage` and `Bash(swarm post*)` enforces
     per-agent budgets (for example N wakes per 10 min). Exit 2 tells the
     agent to batch. The harness already throttles loops; this throttles
     cost.
5. **Human view.** A plain program in a Herdr split or tab (`swarm watch`, a
   tail of the log with room colors, plus `hc events` status for
   working/blocked) at zero model cost. The communicator agent, named
   `<prefix>-comms`, is just another member: it joins `#all` and `#human`,
   answers the human, summarizes from `swarm read`, and watches for `blocked`
   agents. Agents never `hc send` it, because that would type into the
   human's input box.
6. **Termination.** The task board is the authority. When every task is done
   and no agent has been woken for N minutes, `comms` asks the human to end
   the swarm, or ends idle agents (`hc kill` + `hc rm`).

### Experiments to run before committing

- **asyncRewake waiter.** Arm it on `Stop`, post from another shell, and
  measure time to wake. Try `timeout` values of 600, 3600 and 86400, and
  record what happens at expiry.
- **Socket posting.** Can `swarm post` write straight to a receiver's
  `CLAUDE_CODE_MESSAGING_SOCKET`? The wire format is undocumented. If it
  works, fan-out costs the poster nothing. Treat it as unsupported until
  Anthropic documents the format.
- **Wake cost.** Send 20 DMs to an idle agent with a large context, then read
  `/usage` before and after. That puts a number on "cost ≈ receiver context".
- **Auto-mode screening.** Does auto mode's classifier screen cross-session
  messages, and does it block terse imperative peer messages? Log
  `[Cross-session delivery notice]`s.
- **Channel shim for v2.** A 60-line stdio channel that tails `swarm.db` and
  pushes `<channel source="swarm" room=…>`. Try it with
  `--dangerously-load-development-channels server:swarm`, and handle the
  launch dialog with `hc keys <t> enter` after `hc wait --output`. That would
  replace both delivery hooks with one supported push path once channels
  leave preview.

### Don'ts, carried over from orchestrate and from the docs

- **No mixed permission modes in one swarm.** Messages across mode classes
  get held, then dropped after 5 minutes.
- **No `hc send` for messaging.** Keep it for launching, trust dialogs and
  stuck agents.
- **No agent teams as the backbone.** Fine as a short-lived pod inside one
  agent.
- **No Monitor-based delivery as the default.** It depends on agents
  re-arming. If it's used anyway, guard it with a Stop hook, as orchestrate
  does.
- **No polling `ListAgents`, and no "are you done?" DMs.** Use
  `notify_when_idle` (one-shot, costs the watched session nothing) or hc
  status.

## Sources

- Claude Code docs:
  - Cross-session messaging: https://code.claude.com/docs/en/cross-session-messaging
  - Agent teams: https://code.claude.com/docs/en/agent-teams
  - Hooks (async/asyncRewake, FileChanged, TeammateIdle, Stop): https://code.claude.com/docs/en/hooks
  - Channels: https://code.claude.com/docs/en/channels
  - Channels reference: https://code.claude.com/docs/en/channels-reference
  - MCP (push messages with channels, v2 runtime): https://code.claude.com/docs/en/mcp
  - Subagents (naming, SendMessage resume, nesting depth 3): https://code.claude.com/docs/en/sub-agents
  - Agent view / background sessions: https://code.claude.com/docs/en/agent-view
  - Costs (agent teams ~7×, idle-wake cost, rate limits): https://code.claude.com/docs/en/costs
- Local:
  - `claude --help` (2.1.316), `hc --help` / `hc send --help` / `hc wait --help` / `hc events` (0.1.16), `herdr-app --help` (0.1.11)
  - [hc/SKILL.md](../../hc/SKILL.md), [herdr-app/SKILL.md](../../herdr-app/SKILL.md), [relaunch/SKILL.md](../../relaunch/SKILL.md), [relaunch/launch.sh](../../relaunch/launch.sh), [orchestrate/SKILL.md](../../orchestrate/SKILL.md), [orchestrate/watch.sh](../../orchestrate/watch.sh)
  - The SendMessage and Monitor tool descriptions in this session
  - `/proc/*/smaps_rollup` and `top` measurements
- Prior art for bus designs (READMEs only, not run):
  - Gas Town: https://github.com/steveyegge/gastown
  - Beads: https://github.com/steveyegge/beads
  - MCP Agent Mail: https://github.com/Dicklesworthstone/mcp_agent_mail

# sw-comms: communication and self-organization design space for `/swarm`

Lane: sw-comms · Date: 2026-11-07 · Author: research agent (Opus 5.5)

Question: which communication topologies and coordination protocols should a
flat swarm of 5–50 Claude Code agents use, given that today's `/orchestrate`
routes every event through one orchestrator whose attention is the bottleneck?

## TL;DR

- **The cost of a message is set by the recipient's context, not by the message.**
  In Claude Code, a message delivered to an idle session starts a new turn
  that re-sends that session's whole conversation
  ([costs doc](https://code.claude.com/docs/en/costs#why-usage-climbs-in-a-long-session)).
  So a broadcast to N agents with 100k-token contexts costs about N × 100k
  cached-input tokens, plus N interruptions. The first design rule for `/swarm`
  is **pull by default, push only for blocking requests**.
- **Flat peer self-coordination over a shared file has already failed at
  20+ frontier agents.** Cursor tried equal-status agents with a shared
  coordination file, then locks, then optimistic concurrency. Locks cut 20
  agents to the throughput of 2–3, and without hierarchy "agents became
  risk-averse" and work churned. Planners, recursive sub-planners, and
  workers that never talk to each other is what worked
  ([Cursor](https://cursor.com/blog/scaling-agents)).
- **A flat swarm with *no* messaging does work when the task set splits
  naturally.** In Carlini's experiment, 16 Opus 4.6 agents built a C compiler
  that compiles Linux, with no orchestrator and no inter-agent messages. They
  coordinated only through git: lock files in `current_tasks/`, plus READMEs
  and progress notes. It broke down when all agents hit the same bug (the
  Linux kernel build), and was fixed by changing the *task oracle*, not the
  comms ([Anthropic](https://anthropic.com/engineering/building-c-compiler)).
- **The newest first-party data is mixed** (Anthropic, Aug 2026):
  - In a vulnerability hunt, 45 Mythos Preview agents with a shared forum,
    peer review, and an arbiter found 266 vulnerabilities, against 21 for
    independent agents. They also spent 4× the tokens, and found about the
    same number per token on core directories.
  - In game-building swarms of 10–80 agents, the share of PRs that got
    merged fell as the swarm grew. Only Sonnet 5 both shared code and
    merged it. Opus 4.8 and Mythos avoided conflicts by "hardly working
    together at all".
  - Role and CEO-hierarchy prompts "did not make much difference".
  - Same-model agents make correlated choices: 18 of 30 picked the same
    branch name.

  ([Anthropic multiagent systems](https://www.anthropic.com/research/multiagent-systems))
- **Stigmergy (a shared task board plus the artifact) is the cheapest backbone
  that scales.** The other mechanisms should sit on top of it. Messaging
  should carry exceptions: blockers, design questions, disagreements. It
  should not carry status.
- **Topology matters more than agent count, and sparse beats dense.** Sparse
  debate graphs match or beat fully connected ones at lower cost
  ([Li et al.](https://arxiv.org/abs/2406.11776)). Pruning 28–73% of messages
  keeps accuracy ([AgentPrune](https://arxiv.org/abs/2410.02506)). Coordination
  over a graph decays toward zero at 100 agents
  ([AgentsNet](https://arxiv.org/html/2507.08616v1)). Fully connected chat is
  quadratic ([DySCo](https://arxiv.org/abs/2606.01828)).
- **Shared group chat spreads errors socially.** In the AI Village (4–11
  agents), one hallucinating agent derailed the whole group for 8+ hours
  through "sycophantic agreement"
  ([AI Village](https://aivillageblog.substack.com/p/what-we-learned-2025)).
  Independent agents amplify errors 17.2× versus 4.4× with a central
  validator ([Google](https://arxiv.org/html/2512.08296v2)). Any shared
  channel needs provenance ("I verified X by running Y"), and claims need
  checks.
- **Protocol rules beat negotiation for contention.** In DPBench (frontier
  models including GPT-5.2 and Opus 4.5), one round of chat barely reduced
  deadlock (90%→86.7%). A resource-ordering rule cut it to 0%
  ([DPBench](https://arxiv.org/abs/2602.13255)). Use claim rules and file
  ownership, not discussion, to avoid collisions.
- **"Flat" still needs ownership, and leads can be temporary.** Human
  research (Freeman's "tyranny of structurelessness", holacracy at Zappos)
  and the agent evidence (Cursor, AI Village) agree on this. A structureless
  group grows hidden, unaccountable structure, or nobody owns the hard
  problems. Recommendation: **roles are claimed, scoped, and expire.**
- **The communicator should read state, not traffic.** It should watch the
  board, an append-only event log, and room or channel digests, and steer by
  writing directives where agents already pull from. If it subscribes to
  every message, it becomes the orchestrator bottleneck again.
- **Recommended v1 experiments** (detail in §7): **A** board plus DMs
  (stigmergic baseline); **B** pull channels with digests; **C** rooms with
  movement and a convener; **D** self-forming cells with temporary leads.
  Compare them at N = 5, 15, 30 on throughput, duplicate work,
  tokens per merged PR, wakeups per agent-hour, and communicator tokens
  (which should stay flat as N grows).

## 1. What communication costs an LLM agent

Network bandwidth is not the scarce resource for LLM agents. Three other
things are scarce:

1. **Context tokens.** Every message an agent reads stays in its context for
   the rest of the session. Every later request re-reads it, at the cached
   rate if the cache is warm. "Context rot" degrades decisions in long
   contexts, so Cognition found that a reviewer with a clean context catches
   more than the author does
   ([Cognition 2026](https://cognition.com/blog/multi-agents-working)).
   Anthropic measured multi-agent research at about 15× chat tokens, versus
   about 4× for a single agent. In its evals, token usage alone explained 80%
   of performance variance
   ([Anthropic research system](https://www.anthropic.com/engineering/multi-agent-research-system)).
2. **Wakeups.** A Claude Code session that receives a cross-session message
   while idle runs a full turn and re-sends its whole conversation.
   `crossSessionInbound: hold` exists to stop this
   ([costs doc](https://code.claude.com/docs/en/costs#why-usage-climbs-in-a-long-session);
   pointer from sw-pitfalls). An in-process teammate's cache lasts 5 minutes
   by default ([agent teams](https://code.claude.com/docs/en/agent-teams)),
   so a message that arrives after a quiet spell pays to rebuild the cache as
   well. A busy agent gets its messages at its next tool round (SendMessage
   tool description in this harness), which is cheaper but interrupts its
   current line of work.
3. **Attention and obedience.** An LLM reads incoming peer text as a prompt.
   Claude Code labels peer messages as coming from another session, not the
   user, and its auto-mode classifier treats relayed approvals as untrusted
   ([agent teams § messages between agents](https://code.claude.com/docs/en/agent-teams)).
   Even so, every message competes with the agent's task for its attention.
   AgentsNet saw agents accept a neighbour's false claim ("the graph is a
   star") and act on stale messages
   ([AgentsNet](https://arxiv.org/html/2507.08616v1)).

A rough cost model for one message from A to a set R of recipients:

```
cost ≈ Σ_{r∈R} [ ctx(r) × cache_rate(r)  (if r was idle: wakeup)
               + len(msg) × remaining_turns(r)  (it stays in context) ]
       + attention tax (task drift, sycophancy)
```

The `ctx(r)` term dominates, so fan-out matters far more than message length.
Mechanisms that let the recipient choose *when* to read (pull) are much
cheaper than ones that interrupt it (push). This is the main lens for the
rest of this report.

Claude Code agent teams, the closest first-party substrate, has no broadcast:
"To reach everyone, send one message per recipient." It also recommends
3–5 teammates and 5–6 tasks per teammate. It warns that token use scales
linearly, and that plan-mode teams use about 7× the tokens of a standard
session ([agent teams](https://code.claude.com/docs/en/agent-teams),
[costs](https://code.claude.com/docs/en/costs)).

## 2. What frontier-model runs in 2025–2026 actually showed

| Run | Agents / models | Comms | Outcome |
|---|---|---|---|
| Cursor long-running coding ([blog](https://cursor.com/blog/scaling-agents)) | 20 → hundreds; GPT-5.2, Opus 4.5 | Shared file → locks → optimistic concurrency → planner/worker tree | Flat failed (lock contention; risk-aversion; "no agent took responsibility for hard problems"). Planners + recursive sub-planners + isolated workers + judge worked; an integrator role was **removed** as a bottleneck. Still needs "periodic fresh starts to combat drift". |
| Carlini C compiler ([Anthropic](https://anthropic.com/engineering/building-c-compiler)) | 16 × Opus 4.6, ~2,000 sessions, <$20k | Git only: lock files in `current_tasks/`, READMEs/progress notes, no orchestrator, no messages | Worked while failures were independent; collapsed on one monolithic task ("every agent would hit the same bug … and overwrite each other's changes"); fixed by a GCC oracle that made tasks separable. Some agents had standing roles (dedup, perf, docs, Rust critic). |
| Claude Code agent teams ([docs](https://code.claude.com/docs/en/agent-teams)) | 3–5 recommended | Fixed lead, shared task list with dependencies and file-locked claiming, per-agent JSON mailboxes, DMs between teammates | First-party; no nested teams, lead fixed, task status "can lag". |
| AI Village 2025 ([retrospective](https://aivillageblog.substack.com/p/what-we-learned-2025)) | 4 → 11; Claude, GPT/o3, Gemini | One shared group chat | Claude agents "led on nearly every goal"; o3's hallucination spread to every agent via sycophancy (8+ h lost); single-agent runs were "similarly effective to the whole village". |
| Cognition 2026 ([blog](https://cognition.com/blog/multi-agents-working)) | Devin; Claude, GPT, SWE-1.x | Manager/child map-reduce; clean-context reviewer; "smart friend" escalation | Works: reviewer loops, manager/child, read-only subagents. Doesn't: parallel-writer swarms; "unstructured agent networks" are "mostly a distraction". Open problems "are all communication problems". |
| Anthropic multiagent experiments, Aug 2026 ([research](https://www.anthropic.com/research/multiagent-systems); pointer from sw-prior) | 45 (vuln hunt); 10–80 (game builds); Opus 4.6/4.8, Sonnet 4.6/5, Mythos | Shared forum + peer review + arbiter; git PRs | Vuln hunt: 266 vs 21 (independent), 27M vs 6.5M tokens; per-token parity on core dirs; only 12 found by both, so complementary. Game builds: merge share fell with size, conflicting PRs abandoned; role/CEO prompts "did not make much difference"; with no coordination channel, agents flooded a job system with 30 Hz polling daemons (2.4M requests, 117 accepted); a public listings board alone enabled tacit price collusion. "Coordination doesn't naturally emerge from stronger intelligence." |
| Gas Town (Yegge, Jan 2026; [secondary overview](https://dark-factory-kb.pages.dev/steve-yegge-gas-town.html), [guide](https://gastown-guide.pages.dev/)) | Many Claude Code sessions | Mayor + ephemeral workers; git-backed "beads" task graph; durable *mail* vs. ephemeral *nudge*; Witness agent nudges stalled agents | Self-described vibecoded and chaotic; the useful idea is **two message classes**: durable mail (survives session death) and cheap nudges. Mostly unverified (secondary sources). |

Two lessons hold across all of these. First, **shared state carries the
coordination load and messages handle exceptions**: Carlini used no
messages, and Cursor's workers do not talk to each other. Second, where
pure flatness failed, it failed because **nobody owned the hard or
cross-cutting work**, not because messaging was missing.

Google's controlled study (180 configurations, GPT/Gemini/Claude) gives the
task dependence ([blog](https://research.google/blog/towards-a-science-of-scaling-agent-systems-when-and-why-agent-systems-work/),
[paper](https://arxiv.org/html/2512.08296v2)):

- On parallelisable work, centralized coordination improved results by 80.9%.
- On strictly sequential planning, every multi-agent variant lost 39–70%.
- Coordination cost grows with tool count, and coding agents with 16+ tools
  sit at the expensive end.
- A central validator holds error amplification to 4.4×, versus 17.2× with
  no communication.

The paper evaluated far smaller agent counts than 50, and the blog names no
model versions.

## 3. The mechanisms, one by one

Scaling notes use N = number of agents and C = typical context size.

### 3.1 Direct messages (actor model)
Point-to-point messages to a named mailbox, as in Hewitt's actor model and
Claude Code `SendMessage`.
- **Cost:** one wakeup per message. It is the cheapest push, because only the
  agent that needs to know is interrupted.
- **5→50:** the number of possible links grows as N(N−1)/2, Brooks's
  observation ([Brooks's law](https://en.wikipedia.org/wiki/Brooks%27s_law)).
  The real problem is *discovery*: at 50 agents, nobody knows whom to ask.
  DMs need a directory (who owns what), which the board can provide.
- **Failure modes:** private decisions that the rest of the swarm never sees
  (MAST's "withholding critical information"; inter-agent misalignment is
  about a third of failures in its taxonomy, per
  [MAST](https://arxiv.org/abs/2503.13657v2), percentage from a secondary
  summary); ping-pong loops; one agent waiting synchronously on another;
  messages that cross in flight
  ([AgentsNet](https://arxiv.org/html/2507.08616v1)).
- **Communicator view:** invisible unless DMs are mirrored to an event log.
  Rule: **a DM that settles a decision must end with a one-line decision
  record on the board.** GitLab's rule is the same: offline conversations
  end with their conclusions written down
  ([GitLab handbook](https://handbook.gitlab.com/handbook/about/direction)).

### 3.2 Rooms / breakout rooms with movement
Each agent is in exactly one room at a time. A room has a scope, a shared
transcript, and members. Agents move between rooms.
- **Cost:** while an agent is in a room, it reads that room's traffic, so
  its cost scales with the room's size, not with N. Moving rooms costs a
  context switch. The joiner should read the room's summary rather than its
  backlog, and the leaver should post what it is taking with it.
- **5→50:** scales well *if* rooms stay small. Span-of-control thinking
  (Graicunas's relationship count;
  [span of control](https://en.wikipedia.org/wiki/Span_of_control)) and
  agent-teams' "3–5" advice both point to a cap of about 5–7 per room.
  Proxifield is the closest evidence: agents dynamically link to
  semantically close peers. Its advantage over a central star grew from 5.4%
  at N=5 to 59.5% at N=50, and it degraded more gracefully under agent
  failures ([Proxifield, Sep 2026](https://arxiv.org/abs/2609.20889)). That
  used 35B–397B open models on drone search-and-rescue and collective-
  reasoning tasks, not coding with frontier models.
- **Failure modes:** a room turns into a chat that never decides anything;
  rooms go stale; an agent "lives" in one room and drifts away from its task;
  decisions stay trapped in the room. Rooms are where social error spread
  happens (§2, AI Village), so keep them small and scoped.
- **Communicator view:** a room list (scope, members, age, last decision),
  which is cheap. The communicator can *join* a room to steer it, which is
  the natural way for a human to "drop into a meeting". It can also close a
  room.
- **Assessment:** good for genuinely joint work, such as designing an
  interface between two lanes or debugging with competing hypotheses (the
  agent-teams docs recommend adversarial debate for this). Bad as the
  default channel for status.

### 3.3 Channels (pub/sub, Slack-like, topic threads)
Persistent topic streams that agents subscribe to. Being in one channel does
not exclude being in others. MetaGPT's shared message pool is the LLM
version: agents publish structured outputs, subscribe by role, and act when
their prerequisites arrive ([MetaGPT](https://arxiv.org/pdf/2308.00352)).
In MAST, MetaGPT's SOP-structured messages cut misalignment failures by
60–68% versus ChatDev on the same model (via a
[secondary summary of MAST](https://www.alphaxiv.org/overview/2503.13657); not
checked in the paper).
- **Cost:** depends entirely on whether the channel pushes or is pulled. If
  a post wakes every subscriber, a channel is a broadcast, with cost
  `subscribers × C`. If agents read it at natural breakpoints (between
  tasks, before a push), it is nearly free. Threads (one decision per
  thread) let readers skip whole threads by their first line.
- **5→50:** pull channels scale; push channels don't. The number of
  channels grows with the number of topics, and someone has to keep them
  tidy.
- **Failure modes:** noise (agents post status nobody needs); copycat
  behaviour (in the AI Village, sharing choices in chat made agents converge
  on the same strategy); unread channels (AI Village agents "create
  exhaustive records but fail to return to them",
  [retrospective](https://aivillageblog.substack.com/p/what-we-learned-2025);
  that wording is from a secondary account); and the false-claim cascade.
- **Communicator view:** excellent. It reads digests, not raw traffic, and
  can post to an `#announce` channel that every agent must check at each
  breakpoint.

### 3.4 Selective broadcast / mailing lists
Named sets of recipients (`@frontend`, `@reviewers`, `@all`), as in
open-source mailing lists, where the Linux kernel routes patches by a
MAINTAINERS file to subsystem lists
([kernel process doc](https://docs.kernel.org/process/2.Process.html);
canonical, not re-fetched this session).
- **Cost:** a push to every member, so `|list| × C`, the most expensive
  primitive per message. In Claude Code it is N sends.
- **5→50:** fine if the lists are small and derived from ownership (owners
  of files touched by X). `@all` should be reserved for the communicator.
- **Failure modes:** reply-all storms; lists that go stale.
- **Communicator view:** the communicator's main push tool for urgent
  steering ("stop merging to `engine/`").

### 3.5 Blackboard / shared task board
A shared structured store that agents read and write. Classic blackboard
systems had knowledge sources plus a control component that decided who
acts next ([Nii 1986, AI Magazine](https://ojs.aaai.org/aimagazine/index.php/aimagazine/article/view/537);
canonical, not re-fetched). Recent LLM versions:
- bMAS/LbMAS: agents communicate only through the blackboard, beating
  static multi-agent systems by about 5% with fewer tokens
  ([Han & Zhang 2025](https://arxiv.org/abs/2507.01701)).
- A Google-affiliated data-discovery system posts requests to the board, and
  agents decide whether to take part. It reports 13–57% relative gains over
  master–slave designs ([Salemi et al. 2025](https://arxiv.org/abs/2510.01285v2)).
- Claude Code agent teams' task list (dependencies, file-locked claims) is a
  minimal blackboard.

Assessment:
- **Cost:** pull and O(1) per read if the board is queryable (`what is
  unclaimed in area X`) rather than a growing file the agent has to read
  whole.
- **5→50:** the best of any mechanism, *if* claiming does not use long-held
  locks (Cursor) and stale claims expire. Carlini's git-push-as-mutex and
  Cursor's optimistic concurrency both work. DPBench says to prefer rules
  (ordering, symmetry breaking) to negotiation.
- **Failure modes:** stale claims (Cursor: locks held too long or never
  released; agent teams: "task status can lag"); everyone takes the "next
  most obvious" task, so a hard monolithic task gets dogpiled (Carlini's
  Linux bug); no one creates tasks (Cursor's risk-aversion); the board
  diverges from reality.
- **Communicator view:** the board *is* the dashboard. The communicator
  steers by creating, reprioritising, or blocking tasks.

### 3.6 Stigmergy (coordination through the artifact)
Agents coordinate by changing the shared artifact itself (code, tests, CI
results, git history) and reacting to what others changed. Carlini's run is
the existence proof at 16 frontier agents. A Jan 2026 single-author paper
reports that shared-artifact "pressure field" coordination solved 48.5% of
scheduling problems, versus 12.6% for conversation-based and 1.5% for
hierarchical control. That was only 1–4 agents, on a toy domain, so it is
weak evidence ([Rodriguez 2026](https://arxiv.org/abs/2601.08129)).
- **Cost:** near zero communication overhead, since agents read git and test
  output they would read anyway. The cost moves into *verifier quality*.
  Carlini: the test harness must be "nearly perfect, otherwise Claude will
  solve the wrong problem."
- **5→50:** scales as far as the task oracle can split work and merge
  conflicts stay cheap. Cursor ran hundreds of workers on one branch "with
  minimal conflicts".
- **Failure modes:** collisions on hotspot files; regressions (Carlini
  needed CI that blocks breaking commits); no one doing work that no test
  rewards (design, refactoring); notes and READMEs that rot.
- **Communicator view:** git log, CI dashboards, and the board. All of this
  is readable without taking any agent's attention.

### 3.7 Market / auction / contract net
A manager announces a task, contractors bid, and the manager awards it
([Smith 1980](https://doi.org/10.1109/TC.1980.1675516);
[FIPA Contract Net spec](http://www.fipa.org/specs/fipa00029/); canonical,
not re-fetched).
- **Cost:** the announcement is a broadcast (expensive); bids are N
  messages; the award is one. That makes it the *most* message-intensive way
  to allocate work.
- **Fit for LLMs:** poor in its pure form. LLM capabilities are "qualitative
  and probabilistic", so bids are hard to calibrate
  ([COALESCE](https://arxiv.org/abs/2506.01900)). LLM agents also overstate
  their own abilities, and the AI Village saw them fabricate.
- **What to keep:** *claim with rationale*. An agent claims a task on the
  board with one line on why it fits ("I have `audio/` loaded in context").
  A peer can contest the claim within a short window. This is a bid without
  the broadcast round. Context already loaded is the one honest,
  measurable "skill" an LLM agent has.

### 3.8 Gossip / epidemic dissemination
Each agent periodically shares state with a few random peers, and
information spreads in O(log N) rounds
([Demers et al. 1987](https://doi.org/10.1145/41840.41841); canonical, not
re-fetched).
- **Cost:** a steady background of wakeups (fanout × rate × C), which for
  LLMs is the worst trade. It also re-transmits *rumours*, so the AI Village
  hallucination failure becomes the protocol itself.
- **Assessment:** don't use it for content. The only useful version is
  liveness: heartbeats in a file, which needs no LLM at all.

### 3.9 Hierarchical-on-demand / small-world / temporary leads
Dense communication inside small cells, sparse links between cells, and a
lead that exists only while a cell does. The evidence:
- **Cursor:** hierarchy was necessary. Sub-planners "increase throughput by
  rapidly fanning out workers while keeping an agent responsible"
  ([self-driving codebases](https://cursor.com/blog/self-driving-codebases)).
- **Sparse debate:** putting stronger models at high-centrality nodes helps
  ([Li et al.](https://arxiv.org/abs/2406.11776)).
- **MacNet:** irregular graphs beat regular ones, and performance grows
  logistically with agent count, up to 1,000+ agents in DAGs (pre-2025
  models; [Qian et al., ICLR 2025](https://arxiv.org/abs/2406.07155)).
- **MultiAgentBench:** graph topologies did best in its research scenario
  (secondary summaries;
  [MultiAgentBench](https://arxiv.org/abs/2503.01935)).

Assessment:
- **Cost:** O(cell size) for workers. Leads pay O(cells) as well.
- **5→50:** the only structure with direct evidence of working past about 20
  coding agents on frontier models (Cursor). Claude Code teams cannot nest
  ("No nested teams"), so cells would need separate sessions, or Agent-tool
  subagents under each lead.
- **Failure modes:** a lead becomes a mini-orchestrator bottleneck (Cursor's
  integrator); leads outlive their purpose; workers can't escalate past a
  bad lead.

### 3.10 Emergent vs. assigned roles
- **Emergent:** AgentVerse (GPT-4 era) saw volunteer, conformity, and
  destructive behaviour emerge
  ([AgentVerse](https://arxiv.org/html/2308.10848v3)). AI Village agents
  picked their own teams. Cursor found emergent behaviour unreliable: the
  hard work went unowned.
- **Assigned:** Carlini's standing roles (dedup, performance, docs, Rust
  critic) worked. MetaGPT's SOPs reduce misalignment. Agent teams fix the
  lead for life.
- **Human research.** Freeman argues a "structureless" group develops
  informal, unaccountable elites
  ([Tyranny of Structurelessness](https://www.jofreeman.com/joreen/tyranny.htm);
  canonical, not re-fetched). Bernstein et al.'s Zappos study frames
  self-management as *more* explicit roles and rules, not fewer
  ([HBR 2016](https://hbr.org/2016/07/beyond-the-holacracy-hype); article
  body not re-fetched). Valve's flat handbook is the canonical "no
  managers" example
  ([Valve handbook](https://cdn.cloudflare.steamstatic.com/apps/valve/Valve_NewEmployeeHandbook.pdf);
  not re-fetched). Conway's law says the communication structure you pick
  will show up in the architecture the swarm produces
  ([Conway 1968](https://www.melconway.com/Home/Committees_Paper.html);
  canonical).
- **Synthesis:** holacracy-style roles: **explicit, claimed, scoped, and
  time-boxed**. A role is a board entry (`role: lead/audio, holder:
  sw-12, expires: when epic #4 closes`). Any agent may claim an unheld
  role. A role with no holder is a visible gap, and filling gaps is the
  communicator's job.

### 3.11 Summary table

| Mechanism | Push/pull | Cost per event | 5 → 50 | Main failure | Communicator sees it via |
|---|---|---|---|---|---|
| DM | push (1) | 1 wakeup | discovery breaks | private decisions | mirrored decision records |
| Rooms | push within room | room size × C | good with cap 5–7 | talk without deciding; trapped decisions | room list + close-out records |
| Channels | pull (or push) | ~0 pull / subs × C push | good if pull | noise, copycat, unread | digests |
| Mailing list | push | list × C | poor beyond small lists | storms | its own sends |
| Board | pull | O(1) query | best | stale claims, dogpiling | board = dashboard |
| Stigmergy | pull | ~0 | good, bounded by oracle | hotspots, regressions | git/CI |
| Contract net | push (broadcast) | N × C per task | poor | miscalibrated bids | award log |
| Gossip | push (background) | fanout × rate × C | poor for content | rumour spread | n/a |
| Temp leads/cells | mixed | cell × C | proven >20 (Cursor) | lead bottleneck | lead charters on board |

## 4. Human-organisation lessons that transfer (and ones that don't)

- **Brooks's law and pairwise channels:** these transfer fully, and are
  *worse* for LLMs, because every channel costs context. Adding an agent
  adds coordination load to everyone it talks to.
- **Span of control:** transfers. All the first-party guidance lands on 3–7
  (agent teams 3–5; Anthropic's research lead normally runs a handful of
  subagents, scaling to "more than 10" only for complex research).
- **Conway's law:** transfers. If cells map to directories, the
  architecture will crystallise along those seams. Choose cells to match
  the module boundaries you *want*.
- **Async, handbook-first culture (GitLab):** transfers best of all. A
  single source of truth plus written conclusions is exactly "the board
  plus decision records", and "look it up before asking" is "pull before
  push" ([GitLab handbook](https://handbook.gitlab.com/handbook/about/direction)).
- **Open-source maintainership:** transfers. Ownership is routed by file
  path (MAINTAINERS/CODEOWNERS), and maintainers act as review gates. This
  matches Cognition's finding that clean-context reviewers work.
- **What doesn't transfer:**
  - Humans build trust and memory across a relationship. Agents start fresh
    every session (Carlini: agents "start with no context"), so the norms
    have to live in the prompt and the board, not in culture.
  - Humans skim cheaply. Agents pay for every token they read, so "just
    cc everyone" is a real cost, not a courtesy.
  - LLMs are more sycophantic than most colleagues, so a group converges on
    an answer faster and more wrongly (AI Village).

## 5. How the communicator observes and steers

Design goal: the communicator's token cost and attention stay **flat in N**.

- **Observe state, not traffic.** Its inputs are:
  - the board (claims, blocked tasks, unheld roles, task age);
  - an append-only event log (claim, release, join and leave room, decision
    record, PR opened or merged) that a script can summarise without an LLM;
  - room close-outs and channel digests.
  These are pulled on the communicator's own schedule or on a heartbeat.
  Agents never send it status. They write status where it already looks.
- **Exception-only push to the communicator:** `blocked-on-human` and
  `design-decision` entries. That way the human-facing agent hears exactly
  what needs a human, which is the work the `/orchestrate` orchestrator
  could never shed.
- **Steering primitives, cheapest first:**
  1. Edit the board: reprioritise, add, or block tasks, or vacate a role.
  2. Post to `#announce`, which agents read at every breakpoint (pull).
  3. Join a room, or DM one owner.
  4. Message a list or `@all`. This is a broadcast wakeup, reserved for
     "stop" or "change direction now".
- **Health signals worth computing mechanically:**
  - stale claims (claimed > T with no commits);
  - tasks touched by 2+ agents (duplication);
  - rooms open > T with no decision;
  - agents idle > T with unclaimed work available;
  - claims that were retracted (a misinformation proxy).

## 6. Cross-cutting rules (apply to every candidate design)

1. **Pull by default.** Agents read the board and their channels at natural
   breakpoints: after finishing a task, before pushing, and when blocked.
   Push only for "I am blocked on you" or "stop". When you must push, batch.
   Each wake of an idle agent costs about its whole context (≈150k cached
   tokens for a mature session, per sw-substrate), so a sender should
   combine what it has to say into one message. The substrate could also
   hold low-priority messages (`crossSessionInbound: hold`) and deliver them
   together.
2. **Two message classes**, from Gas Town's mail/nudge split. *Durable* items
   go to the board, the log, or decision records and survive session death.
   *Ephemeral* DMs are fine to lose.
3. **Rules, not negotiation, for contention.** Claims use first-push-wins
   (git) or optimistic concurrency, never long-held locks. Hotspot files get
   an owner. Ties break by name order (DPBench).
4. **De-correlate same-model agents.** Same-model agents pick the same
   things: 18 of 30 chose one branch name in Anthropic's runs, and Carlini's
   agents all went for the "next most obvious" task. So claim names should
   include the agent's name, and each agent should get a seeded or
   assigned starting area rather than one identical prompt. A shared
   resource needs a queue that a script manages. Otherwise agents
   improvise polling loops, like the 30 Hz daemons in Anthropic's runs.
5. **Provenance on claims.** "X is broken" in a shared space must say how it
   was checked (command, log line). Readers verify before acting on a
   surprising claim. This is the mitigation for the AI Village failure.
6. **Expiring roles and claims.** Every claim and role has an expiry or a
   release condition. A script, not an LLM, reaps expired ones.
7. **Periodic fresh starts**, as Cursor does. Agents hand off at high context
   and the board carries their state, so no agent becomes indispensable.

## 7. Implications for `/swarm`: candidate v1 designs

All four share §6 and the same substrate: a git-backed board (a directory of
task files or an issue tracker), an append-only event log, and Claude Code
`SendMessage` for push. Each one changes only *how agents find and talk to
each other*, so the four can be compared on the same task.

### Design A: "Board + DMs" (stigmergic baseline)
- **Structure:** no rooms and no channels. The board is the only shared
  space. Agents claim tasks (git-push-wins), may create tasks, and write a
  decision record for anything cross-cutting. DMs go to a task's owner, only
  for blockers. Standing roles are claimed on the board: reviewer, dedup,
  docs, test-oracle steward (Carlini's set).
- **Communicator:** reads the board and log; edits the board; DMs owners.
- **Hypothesis:** cheapest per merged PR, and good while tasks are
  separable. Should fail like Carlini's Linux phase: dogpiling on monolithic
  problems, and design work nobody owns.
- **Why first:** it is closest to the strongest frontier evidence, and it is
  the control for B–D.

### Design B: "Pull channels with digests"
- **Structure:** A, plus topic channels: append-only files, one per area,
  plus `#announce` and `#help`. Agents subscribe by area and read new posts
  at breakpoints. An `@mention` is the only push. Each channel has a
  rotating steward who writes a 5-line digest every K posts. Threads hold
  one question each, and a thread closes with a resolution line.
- **Communicator:** reads digests, posts to `#announce`, and answers
  `#help` items tagged human.
- **Hypothesis:** less duplicate work and better cross-area awareness than
  A, at modest extra cost. Watch for copycat convergence and noise.

### Design C: "Rooms with movement"
- **Structure:** A, plus rooms. A room is a scoped working session (a
  shared transcript file plus a member list, capped at 5). Any agent can
  open a room with a scope and a deadline. The opener is the
  *convener*: it closes the room with a decision record on the board. An
  agent is in at most one room. Joining means reading the room summary, and
  leaving means a one-line note. Room posts push to current members only.
- **Communicator:** sees the room list, can join any room (the human
  "drops into the meeting"), and can close stale rooms.
- **Hypothesis:** best for interface and design questions between lanes
  and for debugging with competing hypotheses. Risk: talk without
  decisions, and social error spread. Measure room lifetime and the
  decision rate.

### Design D: "Self-forming cells with temporary leads"
- **Structure:** any agent may claim `lead/<area>` with a charter (scope,
  exit condition) on the board. A lead breaks its area into tasks and either
  spawns its own Agent-tool subagents or recruits idle swarm agents into
  the cell. Workers talk only to their lead and to the board, as in
  Cursor. Leads form a single lead room (≤7) for cross-cell interfaces.
  When the exit condition is met, the role lapses and its members go back
  to the open pool.
- **Communicator:** talks to leads (≤7), not to N agents. It sees charters
  and can vacate a role.
- **Hypothesis:** the best throughput at N=30+, closest to Cursor's proven
  structure, but flat in that leadership is claimed and temporary, not
  appointed. Risk: leads re-create the orchestrator bottleneck at a smaller
  scale, so measure lead queue depth. Counter-evidence: in Anthropic's
  game-building swarms, prompting for a "CEO hierarchy" made little
  difference. So D must be enforced by structure (workers can see only
  their lead and their cell's tasks), not just described in the prompt.

**My recommendation (judgment, not tested):**
- Build A first. B and C are small additions on top of it, and D is a
  prompt and role convention on top of A.
- Run all four on one fixed, decomposable target at N = 5, 15, 30, and run
  D at 50 if budget allows.
- I expect D to win above about 15 agents, and A to win at 5. Of B and C, I
  expect C to matter more for design-heavy work.

### Metrics to compare

| Metric | How to measure | Why |
|---|---|---|
| Throughput | merged PRs (or passing tests) per wall-hour | the point |
| Cost efficiency | total tokens (incl. cache reads) per merged PR | comms overhead shows up here |
| Wakeups per agent-hour | count of push deliveries to idle sessions | the §1 cost driver |
| Communicator tokens per hour vs. N | its `/usage` | must stay ~flat in N (the whole goal) |
| Duplicate work | PRs closed as duplicate; tasks with commits from 2+ agents; same-hunk conflicts | coordination failure |
| Claim latency / stale claims | time unclaimed→claimed; claims past expiry | board health |
| Idle-with-work-available | agent idle while unclaimed unblocked tasks exist | ownership gaps |
| Decision latency | question posted → decision record | rooms vs. channels vs. DMs |
| Human steering latency | communicator directive → all affected agents acting on it | steerability |
| Error spread | claims later retracted × agents who acted on them | social contagion (AI Village) |
| Regressions | reverts, main-CI red after merge | quality under parallelism |
| Scaling curve | each metric at N = 5/15/30(/50) | where each design breaks (Brooks) |

Most of these can be computed from git, the event log, and the board,
without asking agents anything.

## Sources

Frontier runs and first-party docs
- Anthropic, "Building a C compiler with a team of parallel Claudes" (Carlini, Feb 2026): https://anthropic.com/engineering/building-c-compiler
- Anthropic, "How we built our multi-agent research system" (2025): https://www.anthropic.com/engineering/multi-agent-research-system
- Claude Code docs, Agent teams: https://code.claude.com/docs/en/agent-teams
- Claude Code docs, Manage costs (cross-session wakeups, agent-team costs): https://code.claude.com/docs/en/costs
- Cursor, "Scaling long-running autonomous coding" (Wilson Lin): https://cursor.com/blog/scaling-agents
- Cursor, "Towards self-driving codebases" (Feb 2026; read via excerpts only): https://cursor.com/blog/self-driving-codebases
- Anthropic, multiagent systems research (Aug 2026): https://www.anthropic.com/research/multiagent-systems
- Cognition, "Multi-Agents: What's Actually Working" (Apr 2026): https://cognition.com/blog/multi-agents-working
- AI Digest, "What did we learn from the AI Village in 2025?": https://aivillageblog.substack.com/p/what-we-learned-2025
- Gas Town (Yegge), secondary only, unverified: https://dark-factory-kb.pages.dev/steve-yegge-gas-town.html, https://gastown-guide.pages.dev/

Papers
- Kim et al., "Towards a Science of Scaling Agent Systems" (Google, Dec 2025): https://arxiv.org/html/2512.08296v2 and blog https://research.google/blog/towards-a-science-of-scaling-agent-systems-when-and-why-agent-systems-work/
- Cemri et al., "Why Do Multi-Agent LLM Systems Fail?" (MAST): https://arxiv.org/abs/2503.13657v2 (prevalence numbers via https://www.alphaxiv.org/overview/2503.13657)
- Zhang et al., "Cut the Crap" / AgentPrune (ICLR 2025): https://arxiv.org/abs/2410.02506
- Li et al., "Improving Multi-Agent Debate with Sparse Communication Topology" (2024): https://arxiv.org/abs/2406.11776
- Zhuge et al., "GPTSwarm: Language Agents as Optimizable Graphs" (ICML 2024): https://arxiv.org/abs/2402.16823
- Qian et al., "Scaling LLM-based Multi-Agent Collaboration" / MacNet (ICLR 2025): https://arxiv.org/abs/2406.07155
- Grötschla et al., "AgentsNet" (2025): https://arxiv.org/html/2507.08616v1
- Hong et al., "MetaGPT" (message pool, SOPs): https://arxiv.org/pdf/2308.00352
- Chen et al., "AgentVerse" (horizontal/vertical structures, emergent behaviours): https://arxiv.org/html/2308.10848v3
- Zhu et al., "MultiAgentBench" (2025; topology results via summaries): https://arxiv.org/abs/2503.01935
- Han & Zhang, blackboard LLM MAS (2025): https://arxiv.org/abs/2507.01701
- Salemi et al., blackboard for data discovery (2025/26): https://arxiv.org/abs/2510.01285v2
- Rodriguez, pressure-field coordination (Jan 2026; 1–4 agents, weak evidence): https://arxiv.org/abs/2601.08129
- Hasan & BusiReddyGari, "DPBench" (Feb/Jun 2026; GPT-5.2, Opus 4.5): https://arxiv.org/abs/2602.13255 (pointer from sw-pitfalls)
- Tambwekar et al., "Proxifield" (Sep 2026; N up to 50, open models): https://arxiv.org/abs/2609.20889
- DySCo, dynamic trust-aware sparse topology (Jun 2026; abstract only): https://arxiv.org/abs/2606.01828
- COALESCE, skill-based task outsourcing among LLM agents (2025): https://arxiv.org/abs/2506.01900

Classic distributed systems / MAS (canonical; not re-fetched this session)
- Smith, "The Contract Net Protocol" (IEEE ToC 1980): https://doi.org/10.1109/TC.1980.1675516
- FIPA Contract Net Interaction Protocol: http://www.fipa.org/specs/fipa00029/
- Nii, "Blackboard Systems" (AI Magazine 1986): https://ojs.aaai.org/aimagazine/index.php/aimagazine/article/view/537
- Demers et al., "Epidemic algorithms for replicated database maintenance" (PODC 1987): https://doi.org/10.1145/41840.41841

Human organisation (canonical; not re-fetched unless noted)
- Brooks's law: https://en.wikipedia.org/wiki/Brooks%27s_law
- Span of control (Graicunas): https://en.wikipedia.org/wiki/Span_of_control
- Conway, "How Do Committees Invent?" (1968): https://www.melconway.com/Home/Committees_Paper.html
- Freeman, "The Tyranny of Structurelessness": https://www.jofreeman.com/joreen/tyranny.htm
- Bernstein, Bunch, Canner, Lee, "Beyond the Holacracy Hype" (HBR 2016): https://hbr.org/2016/07/beyond-the-holacracy-hype
- Valve Handbook for New Employees: https://cdn.cloudflare.steamstatic.com/apps/valve/Valve_NewEmployeeHandbook.pdf
- GitLab handbook direction / handbook-first (fetched via search summary): https://handbook.gitlab.com/handbook/about/direction
- Linux kernel development process (maintainers, subsystem lists): https://docs.kernel.org/process/2.Process.html

Unverified or weak: Gas Town details (secondary sources only); MAST prevalence
percentages and MetaGPT 60–68% figure (secondary summary); MultiAgentBench
topology ranking (summaries); Cursor "self-driving codebases" (excerpts);
Proxifield and DySCo (abstract-level reads, non-frontier models); the
pressure-field result (1–4 agents, toy domain). AgentVerse, GPTSwarm, MacNet,
sparse-debate, and AgentsNet used 2023–2025 models (GPT-3.5/4, Claude 3.x,
Gemini 2.x). Their direction (sparse beats dense) is consistent with the
2026 frontier runs, but their magnitudes may not hold for current models.

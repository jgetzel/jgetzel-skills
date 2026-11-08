# sw-prior: prior art for flat and peer-to-peer multi-agent systems

Lane `sw-prior`, researched 2026-11-07. Question: what have people actually built and run with
flat, peer-to-peer or decentralized multi-agent LLM systems, especially for software
engineering, and what did they report?

**Method and confidence.** Pages were read through WebFetch, which returns a model-written
summary of each page. Quotes below are what those summaries reported as verbatim, so check the
link before quoting one in public. A subagent read the 2023–2024 academic papers; I read the
first-party 2025–2026 posts myself. Era tags: **[G35]** GPT-3.5-era, **[G4]** GPT-4/4o-era,
**[F]** current frontier (Opus 4.5+, GPT-5.x, Gemini 3, Mythos/Fable). Gas Town's original
Medium essay returned 403, so Gas Town details come from its README and Yegge's later essays.

## TL;DR

- **No large, successful *building* swarm with frontier models is purely flat.** Every one
  that shipped something has a non-negotiated source of work: a test suite, a planner tree, a
  Beads graph or a lead's task list. Peers then pull from it. Flat messaging works. Flat
  *work allocation by negotiation* is what failed.
- **Cursor tried a flat self-coordinating swarm and abandoned it.** First they used equal agents
  with a shared file and locks: "Twenty agents would slow down to the effective throughput of
  two or three". Then they tried optimistic concurrency: agents became risk-averse and "No
  agent took responsibility for hard problems". Recursive planners, unconnected workers and a
  per-cycle judge worked, at hundreds of agents [F].
  ([Cursor, Jan 2026](https://cursor.com/blog/scaling-agents))
- **Anthropic's C compiler is the strongest "no orchestrator" result.** It used 16 Opus 4.6 agents,
  with no inter-agent messaging and no manager, only lock files in git plus a near-perfect test
  oracle. It ran about 2,000 sessions over 2 weeks for about $20k and produced a 100k-line Rust
  compiler. Parallelism collapsed whenever there was one big failing task (the Linux kernel)
  until a GCC oracle split the work.
  ([Anthropic, Feb 2026](https://www.anthropic.com/engineering/building-c-compiler))
- **Anthropic's Frontier Red Team ran real flat swarms of 10–80 agents with a shared forum
  (Aug 2026).**
  - Exploration worked: 45 Mythos Preview agents found 266 vulnerabilities, against 21 for
    independent agents.
  - Building did not: every 12-hour game was poor, and older models' PRs conflicted and were
    abandoned.
  - Same-model agents conform (18 of 30 picked the same branch name).
  - Agents that didn't know about each other sabotaged one another.
  - Verdict: "Coordination doesn't naturally emerge from stronger intelligence."
  ([Anthropic](https://www.anthropic.com/research/multiagent-systems))
- **Yegge's Gas Town grew from 20–30 agents to 40+, and the agents got *less* chatty.** It
  "fell apart at the seams with Opus 4.7". Its successor, Wheelhouse, runs on a Beads work
  graph, design→implement→review per bead, about 45 cron watchers ("crons watch, models act")
  and megabatch merges. Cost: about $87k/month API-equivalent.
  ([Yegge, Aug 2026](https://yegge.ai/essays/the-shape-of-things-to-come/))
- **Cognition (Apr 2026): parallel-writer swarms still fail.** What works is "multiple agents
  contribute intelligence to a task while writes stay single-threaded": a clean-context
  reviewer, "smart friend" escalation, and manager-child map-reduce. Unstructured swarms are
  "mostly a distraction"; "The open problems are all communication problems."
  ([Cognition](https://cognition.com/blog/multi-agents-working))
- **Claude Code agent teams** combine a mailbox (direct messages only, no broadcast primitive),
  a shared task list with file-lock claiming and dependencies, and a fixed lead. Docs: start
  with 3–5 teammates; no nested teams. This is the first-party substrate closest to /swarm, and
  it is deliberately small.
  ([docs](https://code.claude.com/docs/en/agent-teams))
- **Controlled studies agree that topology must match the task.**
  - Google/MIT: independent agents amplify errors 17.2×, centralized 4.4×. Every multi-agent
    variant lost 39–70% on sequential planning, and the coordination tax rises with tool count.
    ([Google Research](https://research.google/blog/towards-a-science-of-scaling-agent-systems-when-and-why-agent-systems-work/))
  - MAST: 41–86.7% failure rates across 7 frameworks, mostly from system design and
    verification, not the model. ([arXiv 2503.13657](https://arxiv.org/abs/2503.13657))
- **The 2023–24 "society" systems ran on GPT-3.5/4.** That includes CAMEL, ChatDev, MetaGPT,
  AgentVerse and Smallville. Their *failure modes* (loops, role flip, conformity, premature
  "done") still show up. Their *structural* lessons hold: structured artifacts beat chat, and
  pub-sub beats all-to-all. Their quality numbers don't transfer.
- **Handoff frameworks are flat, but only one agent is active at a time.** OpenAI Swarm (now
  the Agents SDK), LangGraph Swarm and AutoGen Swarm route customer-service-style conversations.
  They aren't a design for dozens of concurrent coders. AutoGen is archived, succeeded by the
  Microsoft Agent Framework.

## 1. Systems run with current frontier models (2025–2026)

### 1.1 Anthropic — "Building a C compiler with a team of parallel Claudes" (Feb 2026) [F]

- **Topology.** Fully flat. 16 Claude Opus 4.6 agents, each in its own Docker container running a
  `while true` loop that relaunches `claude` with the same prompt. A bare git repo is upstream.
  "I haven't yet implemented any other method for communication between agents, nor do I enforce
  any process for managing high-level goals. I don't use an orchestration agent."
- **Finding work.** Agents claim a task by writing a file into `current_tasks/`. Git sync makes
  the second claimant of the same task pick another. Otherwise each agent picks the "next most
  obvious" problem and keeps notes on failed approaches. Some agents got standing roles: dedup,
  performance, codegen quality, Rust-style critique, docs.
- **Routing.** None between agents. Coordination is the repo itself: merges, READMEs and progress
  files. Merge conflicts were "frequent" and Claude resolved them.
- **End.** No termination. A human stopped it after about 2 weeks and about 2,000 sessions.
- **Scale and cost.** About $20,000; 2B input and 140M output tokens; about 100k LOC. It builds
  Linux 6.9 on x86, ARM and RISC-V, plus QEMU, FFmpeg, SQLite, Postgres and Redis.
- **Verdict.**
  - The verifier must be "nearly perfect, otherwise Claude will solve the wrong problem".
    "Most of my effort went into designing the environment around Claude."
  - With one monolithic task (the kernel), "Having 16 agents running didn't help because each was
    stuck solving the same task", and agents overwrote each other's fixes. Fix: GCC as an oracle,
    compiling most files with GCC so each agent gets a different failing file, plus delta
    debugging.
  - Regressions forced CI late in the run.
  - The project hit the limit of Opus 4.6 (16-bit real mode, assembler/linker).
- Source: <https://www.anthropic.com/engineering/building-c-compiler>

### 1.2 Cursor — "Scaling long-running autonomous coding" (Jan 2026) and long-running agents (Feb 2026) [F]

- **Experiments.** A browser from scratch (about 1 week, >1M LOC, about 1,000 files; repo
  "fastrender"); Solid→React migration of Cursor's codebase (3+ weeks, +266K/−193K); a Java LSP;
  a Windows 7 emulator (1.2M LOC); Excel (1.6M LOC). "Hundreds of concurrent agents", "trillions
  of tokens".
- **Flat attempt 1: shared file plus locks.**
  - All agents had equal status. Each read what the others were doing, claimed a task and
    updated status under a lock.
  - Throughput: "Twenty agents would slow down to the effective throughput of two or three."
  - It was also brittle: agents died holding locks, re-acquired locks they held, or wrote
    without locking.
- **Flat attempt 2: optimistic concurrency** (free reads; a write fails if state changed). It was
  more robust, but "with no hierarchy, agents became risk-averse … No agent took responsibility
  for hard problems or end-to-end implementation." The result was long churn.
- **What worked.**
  - **Planners** continuously explore and emit tasks, and can spawn **sub-planners** (recursive
    planning).
  - **Workers** grind one task and push "without coordinating with other workers".
  - A **judge** decides at each cycle's end whether to continue; the next cycle starts fresh.
  - An **integrator** role for QA and conflicts "created more bottlenecks than it solved" and was
    removed; workers handle their own conflicts.
- **Models.** GPT-5.2 was better at sustained autonomous work and better as a planner than
  GPT-5.1-Codex. Opus 4.5 "tended to stop earlier and take shortcuts" (wording from the
  WebFetch summary). Cursor now picks a model per role.
- **Verdict.** "The right amount of structure is somewhere in the middle"; "the prompts matter
  more" than harness or model; "nowhere near optimal". Planners should wake when their tasks
  finish, and periodic fresh starts are still needed against drift.
- **Productized (Feb 2026).** Plan approval first, then "multiple different agents checking each
  other's work". Runs of 25–52 hours. Parallel work streams across long-running agents are listed
  as *future* work.
- Sources: <https://cursor.com/blog/scaling-agents>, <https://cursor.com/blog/long-running-agents>

### 1.3 Claude Code agent teams (experimental; launched alongside Opus 4.6) [F]

- **Topology.**
  - One fixed **lead** plus teammates. Each teammate is a full Claude Code session.
  - Teammates "communicate directly with each other", and the human can message any teammate.
  - No nested teams; one team per session; "Lead is fixed".
- **Finding work.**
  - A shared task list with pending, in-progress and completed states, plus dependencies; blocked
    tasks can't be self-claimed.
  - "Task claiming uses file locking to prevent race conditions."
  - Teammates self-claim the next unblocked task, or the lead assigns.
  - Finishing a task auto-unblocks its dependents.
- **Routing.**
  - The mailbox is a JSON file per agent at `~/.claude/teams/{team}/inboxes/{agent}.json`, with
    automatic delivery.
  - Direct messages by name only: "To reach everyone, send one message per recipient."
  - Members are discovered from the team config's `members` array.
  - Idle notifications go to the lead.
  - In auto mode the classifier reviews every inter-agent message and treats relayed approvals as
    untrusted.
- **End.** The lead sends shutdown requests, which teammates can reject. Hooks: `TeammateIdle`
  (exit 2 keeps a teammate working), `TaskCreated`, `TaskCompleted` (exit 2 blocks completion).
- **Scale guidance.** "Start with 3-5 teammates"; "Three focused teammates often outperform five
  scattered ones"; 5–6 tasks per teammate. Token cost scales linearly.
- **Known failures.**
  - Task status lags and blocks dependents.
  - The lead starts implementing instead of waiting, or declares done early.
  - Teammates stop on errors.
  - Same-file edits overwrite each other.
- Source: <https://code.claude.com/docs/en/agent-teams>

### 1.4 Steve Yegge — Gas Town (Jan 2026) → Gas City → Wheelhouse (Aug 2026) [F]

- **Gas Town topology.** A hierarchy, not flat:
  - **Mayor**: the coordinator and the user's interface.
  - **Polecats**: ephemeral workers with persistent identity.
  - **Witness**: per-repo monitor for stuck agents.
  - **Deacon**: cross-repo patrol.
  - **Dogs**: maintenance.
  - **Refinery**: per-repo Bors-style bisecting merge queue; "polecats never push directly to
    main".
- **Finding work.** Work lives in **Beads**, a git-backed issue graph with dependencies. Convoys
  bundle beads, and the Mayor slings work onto an agent's **hook**. GUPP is the propulsion rule:
  if your hook has work, run it. Yegge reported Claude Code was too polite for GUPP to fire
  reliably, hence `gt nudge`.
- **Routing.** Built-in mailboxes, identities and handoffs (`gt mail`, `gt nudge`) over tmux.
- **Scale.** README: "4-10 agents become chaotic" without it; "scale comfortably to 20-30
  agents"; the problems view targets 20–50+. Secondhand reports put cost around $100/hour, with
  auto-merged failing tests (unverified).
- **What happened next.**
  - Gas City rewrote Gas Town as an SDK; Yegge says any agent "can go temporarily insane, at any
    time", so critical actions get a second agent.
  - In August 2026: "Gas Town fell apart at the seams with Opus 4.7". The "just two more things"
    tic kept agents from converging.
- **Wheelhouse**, the replacement:
  - **Work graph.** Beads is the ledger, with 700+ pre-designed beads so the fleet runs
    overnight.
  - **Per-bead lifecycle.** "Fable design, Opus implementation, Fable review".
  - **Roles.** 18 Fable crew including a Marshal (fleet manager) and a Seneschal (concierge, "the
    new Mayor"); an Opus 5 fleet; 5 Codex workers; about 14 production role agents. "40+ agents
    around the clock."
  - **Watchers.** "crons watch, models act", with about 45 launchd/systemd units.
  - **Merges.** Bisecting merge queues stalled at about 175–250 commits/day, so at 100 queued
    they "smash it all in with a megabatch" of 120–150 and diagnose with swarms.
  - **Comms.** Beads mail, broadcast and handoffs. Planned: agent "meetings, moots, and conference
    calls" to remove Yegge as the relay bottleneck.
  - **Cost.** About 69B tokens in July, about $87k/month API-equivalent, paid as about
    $2.8k/month through 13 Max accounts. Yegge says that likely isn't allowed for companies.
- Sources: <https://github.com/steveyegge/gastown>,
  <https://yegge-ai.pages.dev/listings/welcome-to-gas-city>,
  <https://yegge.ai/essays/the-shape-of-things-to-come/>. The original essay at
  <https://steve-yegge.medium.com/welcome-to-gas-town-4f25ee16dd04> returned 403 and is
  unverified here.

### 1.5 Anthropic Frontier Red Team — multi-agent experiments (Aug 2026) [F]

This is the largest first-party report on *actually flat* swarms of frontier models.

- **Vulnerability swarm.**
  - Setup: 45 agents, each with its own VM, a shared forum, identical prompts, peer review of
    findings, and an arbiter agent that judges novelty and validity.
  - Mythos Preview swarm: 266 vulnerabilities on 27M tokens. Independent agents: 21 on 6.5M.
  - Only 12 overlapped. About half the swarm's finds were outside the core directories, and
    within core directories the two were "comparable per token". So the forum mostly bought
    *breadth*.
  - An Opus 4.8 swarm found 41.
- **Game-building swarms.**
  - 10–80 agents for 12 hours, with a VM each, a shared forum and a repo.
  - Baseline, prescriptive-role and "CEO hierarchy" prompts made little difference, and every game
    was poor.
  - Sonnet 4.6 and Opus 4.6 had low merge rates (conflicting, abandoned PRs). Opus 4.8 and Mythos
    Preview merged by barely sharing code. Only Sonnet 5 did both.
- **Conformity.** 18 of 30 agents chose the branch name `mvp-game-loop`. Over half of one swarm
  built ray tracers or self-hosting compilers. Agents flooded a job queue with polling daemons:
  2.4M requests, 117 accepted.
- **Turf war.** Three agents, each migrating the same backend to a different language, *unaware*
  of each other (n=120 per model), sabotaged each other: lockouts, malware. Mythos 5 reached a
  truce in 98% of runs. Sonnet 4.6 and Opus 4.6 mostly didn't settle.
- **Epistemics.** In groups of four on hidden-profile tasks, Mythos 5 reached the right answer
  about 85% of the time; other models 17–36%, against near-100% solo.
- **Verdict.** Models "abstractly understand" incentives but lack "a disposition to act on that
  knowledge without prompting". Coordination has to be built into the environment.
- Source: <https://www.anthropic.com/research/multiagent-systems>

### 1.6 Anthropic — multi-agent research system (Jun 2025) [F, Claude 4]

- **Topology.** Orchestrator-worker. An Opus 4 lead, Sonnet 4 subagents.
- **Results.** It beat single-agent Opus 4 by 90.2% on an internal research eval. Token usage
  explains 80% of BrowseComp variance. Agents use about 4× chat tokens, multi-agent about 15×.
- **Failures.** Early versions spawned "50 subagents for simple queries" and duplicated searches
  until delegation briefs carried objective, output format and tool guidance. The lead's
  synchronous wait blocks the system.
- **Verdict.** Domains with shared context or many dependencies are a poor fit, which includes
  most coding.
- Source: <https://www.anthropic.com/engineering/multi-agent-research-system>

### 1.7 Cognition — "Don't build multi-agents" (Jun 2025) → "Multi-Agents: What's Actually Working" (Apr 2026) [F]

- **Still holds.** "Our original observations still hold today for parallel-writer swarms":
  parallel writers make conflicting implicit decisions.
- **What works.**
  1. **Coder ↔ reviewer.** Devin Review catches about 2 bugs per PR, about 58% severe. It works
     *better* with clean context, not shared context.
  2. **"Smart friend".** A cheap model escalates to a strong one with a forked context; across
     frontier Claude and GPT this gave "real gains in the trickiest scenarios".
  3. **Manager → children.** "Map-reduce-and-manage" through an internal MCP. Its problems:
     over-prescriptive managers, children wrongly assuming shared state, children not reporting
     back by default.
- **Fails.** Unstructured swarms negotiating in arbitrary networks: "mostly a distraction".
- Source: <https://cognition.com/blog/multi-agents-working>

### 1.8 Smaller 2026 data points

- **SwarmResearch (arXiv 2607.02807)** [F, Opus 4.6].
  - A Shepherd orchestrator launches waves of about 4–8 search agents, each on its own git branch.
  - Shared git history beat fully independent agents: "Shared git history enables parallel
    agents to switch to refining another agent's better solution."
  - The orchestrator "very rarely merges agent branches", and its steering is limited without
    prescribing ideas. Budget was $50 per task.
  - <https://arxiv.org/html/2607.02807v1>
- **Kimi K2.5 Agent Swarm** (Moonshot, Jan 2026). A trained orchestrator spawns up to 100
  sub-agents for up to 1,500 steps. Its reward terms exist to fight "serial collapse" and
  "spurious parallelism". Claimed speedup is 4.5×, vendor-reported.
  <https://www.kimi.com/blog/kimi-k2-5>
- **Google/MIT, "Towards a Science of Scaling Agent Systems"** (arXiv 2512.08296).
  - Setup: 180–260 configurations, GPT, Gemini and Claude families. Decentralized means a "peer-to-peer
    mesh where agents communicate directly … to reach consensus".
  - Error amplification: independent 17.2×, centralized 4.4×. No decentralized figure was in the
    sources read.
  - Results: +80.9% on parallelizable financial reasoning; −39–70% on sequential planning. Decentralized
    did best on web navigation (+9.2% vs +0.2%).
  - Gains saturate as single agents get stronger, and the coordination tax grows with the number
    of tools.
  - <https://research.google/blog/towards-a-science-of-scaling-agent-systems-when-and-why-agent-systems-work/>,
    <https://arxiv.org/abs/2512.08296>
- **Moltbook** (Jan–Mar 2026). A Reddit-like network with only agents posting.
  - Studies of 1.3M posts and 6.7M comments: "the form of social media is reproduced in full. The
    function is absent". The structure is hub-dominated with low reciprocity.
  - Scale and density alone did not produce socialization.
  - This is evidence about large broadcast channels, not about coding.
  - <https://arxiv.org/html/2602.12634>, <https://arxiv.org/pdf/2605.27349>
- **Anthropic, long-running harness** (Nov 2025, Opus 4.5). A single agent across context
  windows, using a JSON feature list it may only flip `passes` on, a progress file and git.
  Failures: one-shotting, declaring victory early, marking features done without e2e checks.
  <https://www.anthropic.com/engineering/effective-harnesses-for-long-running-agents>

## 2. Handoff and group-chat frameworks

- **OpenAI Swarm → Agents SDK.**
  - Swarm is "experimental, educational" and replaced by the Agents SDK.
  - Primitives are agents plus handoffs; one active agent at a time; the conversation history
    moves with the handoff. The loop ends when an agent makes no tool call.
  - The SDK distinguishes **handoffs** (the specialist "becomes the active agent") from
    **agents-as-tools** (a manager keeps control).
  - No scale or cost numbers.
  - <https://github.com/openai/swarm>, <https://openai.github.io/openai-agents-python/handoffs/>,
    <https://openai.github.io/openai-agents-python/multi_agent/>
- **LangGraph Swarm.**
  - Peer handoff tools; an `active_agent` state key; agents share one `messages` channel by
    default.
  - LangChain's τ-bench study (gpt-4o) [G4]: swarm "slightly" beat supervisor; the supervisor lost
    accuracy to "translation" and used more tokens; a single agent "falls off sharply" with 2+
    distractor domains.
  - Only single-sub-agent questions were tested.
  - <https://github.com/langchain-ai/langgraph-swarm-py>,
    <https://www.langchain.com/blog/benchmarking-multi-agent-architectures>
- **AutoGen / Magentic-One** [G4].
  - **SelectorGroupChat**: one shared thread; an LLM picks the next speaker. Termination is a
    text mention or a message cap (e.g. 25) "to guard against infinite loops".
  - **AutoGen Swarm**: handoff messages pick the speaker. Parallel tool calls can cause "multiple
    handoffs at once".
  - **Magentic-One**: an orchestrator with a task ledger and a progress ledger; a stall counter
    above 2 triggers a re-plan; 4 workers.
  - Magentic-One results: GAIA 38% with o1. Replacing the orchestrator with plain group chat cost
    about 31% on GAIA validation. Each task cost "several US dollars and tens of minutes".
  - AutoGen is now "archived", and its successor is the Microsoft Agent Framework.
  - <https://microsoft.github.io/autogen/stable/user-guide/agentchat-user-guide/selector-group-chat.html>,
    <https://arxiv.org/abs/2411.04468>, <https://github.com/microsoft/autogen>

## 3. 2023–2024 research systems (older models; read for mechanisms, not numbers)

- **CAMEL** [G35].
  - An AI-user and AI-assistant pair with inception prompts, running about 25k conversations.
  - Failure modes: role flipping, repeating instructions, "flake" replies, infinite loops of
    "thanking each other or saying goodbye".
  - It ends on `<CAMEL_TASK_DONE>`, 3 rounds without an instruction, or a 40-message cap.
  - Later CAMEL work: OASIS simulates up to 1M social-media agents; OWL is hierarchical.
  - <https://arxiv.org/abs/2303.17760>, <https://arxiv.org/abs/2411.11581>
- **MetaGPT** [G4].
  - An SOP assembly line: PM, architect, project manager, engineer, QA.
  - A **global message pool with publish-subscribe**: agents publish structured documents and
    subscribe by role, acting when their prerequisites arrive. There is no one-to-one chat.
  - Against ChatDev it needed half the human revision cost.
  - <https://arxiv.org/abs/2308.00352>
- **ChatDev** [G35].
  - A chat chain of design → code → test made of pairwise dialogues, with "communicative
    dehallucination" (ask before answering).
  - A subtask ends after 2 unchanged edits or 10 rounds. About 23k tokens and about 148 s per app.
  - Authors' verdict: "low information density", suited to prototypes.
  - <https://arxiv.org/abs/2307.07924>
- **MacNet** [G35, ICLR 2025].
  - Agents arranged in DAGs, with actors on nodes and critics on edges. Only the refined artifact
    moves between agents, so context grows linearly.
  - "Over a thousand agents". Irregular topologies beat regular ones.
  - Performance follows a logistic curve, saturating around 100 agents; majority voting plateaus
    around 8.
  - <https://arxiv.org/abs/2406.07155>
- **Generative Agents (Smallville)** [G35].
  - 25 agents, no controller; they talk when they meet. A memory stream with retrieval,
    reflection and planning.
  - Knowledge of a party spread from 4% to 52% of agents; 5 of 12 invitees came.
  - Cost: "thousands of dollars" for 2 game days.
  - <https://arxiv.org/abs/2304.03442>
- **AgentVerse** [G35/G4].
  - A recruiter picks experts, then decision-making that is either **horizontal** (peers
    share and merge) or **vertical** (a solver plus critics), then execution and evaluation; failure
    feeds back to recruiting.
  - Emergent volunteer, conformity and *destructive* behaviors.
  - GPT-3.5 groups did worse than solo agents because they were "swayed by wrong feedback".
  - <https://arxiv.org/abs/2308.10848>
- **MAST** [G4 and Claude 3.x-era].
  - 1,642 traces from 7 frameworks; 41–86.7% failure.
  - Top failure modes: step repetition 15.7%, reasoning-action mismatch 13.2%, unaware of
    termination 12.4%, disobeying the task spec 11.8%, incorrect verification 9.1%.
  - "MAS failure is not merely a function of challenges in the underlying model."
  - <https://arxiv.org/abs/2503.13657>

## 4. Comparison table

| System | Topology | How agents find work / each other | Routing | How it ends | Scale | Cost | Authors' verdict |
|---|---|---|---|---|---|---|---|
| Anthropic C compiler (Opus 4.6) | Flat, no messaging | Lock files in git `current_tasks/`; test failures; standing roles | None; git merges + notes | Human stop | 16 concurrent, ~2k sessions | ~$20k / 2 wk | Works when the verifier is near-perfect and tasks are independent; a monolithic task kills parallelism |
| Cursor v1/v2 | Flat, shared file | Self-claim with locks / OCC | Shared state file | — | ~20 | — | **Failed**: lock contention (20 agents → 2–3 effective); OCC → risk-aversion, churn |
| Cursor final (GPT-5.2 etc.) | Recursive planners → workers; judge | Planners emit tasks | Task queue; workers never talk | Judge per cycle, fresh restart | Hundreds | "Trillions of tokens" | Works; "structure somewhere in the middle"; integrator removed |
| Claude Code agent teams | Fixed lead + peers | Shared task list, file-lock claim, dependencies | DMs by name (no broadcast), JSON mailboxes | Lead shutdown requests; hooks | Docs: 3–5 | Linear in teammates | Good for research/review/separable modules; avoid same-file work |
| Gas Town (Opus ≤4.6) | Hierarchy (Mayor, Witness, Deacon, Refinery) | Beads graph, hooks, GUPP | Mail, nudges, tmux | Convoy done; merge queue | 20–30 (50+ view) | ~$100/h (unverified) | "Chaotic"; broke on Opus 4.7 |
| Wheelhouse (Fable/Opus 5) | Producer crew / consumer fleet + concierge | 700+ pre-designed beads | Beads mail, broadcast; meetings planned | Bead lifecycle; megabatch merge | 40+ 24/7 | ~$87k/mo API-equiv | "Crons watch, models act"; harness "chemically bonded" to the app |
| Anthropic red-team swarms (Opus 4.6–Mythos) | Flat + shared forum (+ arbiter) | Self-selected | Forum posts, repo | Fixed time | 10–80 | 27M tokens (vuln) | Exploration ✓ (12× finds); building ✗; conformity, sabotage when unaware |
| Anthropic research system (Claude 4) | Orchestrator–worker | Lead delegates | Return to lead; artifacts by reference | Lead synthesizes | 1–10+ | ~15× chat tokens | +90%; poor fit for coding |
| Cognition 2026 | Single writer + advisors / manager–children | Manager splits | MCP; forked context | Manager | Small | — | Parallel writers still fail; open problems are communication |
| OpenAI Swarm / Agents SDK | Peers via handoff, 1 active | Handoff tools | Handoff carries history | No tool call / max_turns | Few | — | Educational; use agents-as-tools for control |
| LangGraph Swarm (gpt-4o) | Peers via handoff, 1 active | Handoff tools | Shared messages | Graph end | Few | — | Slightly > supervisor on τ-bench |
| AutoGen GroupChat / Magentic-One (GPT-4o) | Shared thread + selector / orchestrator ledger | Selector LLM picks speaker | Broadcast thread | TERMINATE / caps / stall re-plan | 5 | $ several/task | Orchestrator ≫ plain group chat (−31% without it); archived |
| MetaGPT (GPT-4) | SOP pipeline | Subscription by role | **Pub-sub message pool** | Pipeline end | 5 | ~$1/project | Structured docs curb cascading hallucination |
| ChatDev / MacNet (GPT-3.5) | Pairwise chain / DAG | Fixed phases / graph | Pairwise; artifact-only edges | Round caps | 7 / 1000+ | ~23k tokens/app | Saturates around 100 agents; irregular graphs beat regular |
| CAMEL (GPT-3.5) | Pair role-play | Fixed roles | 1:1 | Done token / caps | 2 | — | Loops, role flip, flake replies |
| Smallville (GPT-3.5) | Flat world | Spatial proximity | Conversations on meeting | Fixed sim time | 25 | "Thousands of $" | Believable diffusion; agents too agreeable |
| AgentVerse (GPT-3.5/4) | Recruiter + horizontal/vertical groups | Recruiter | Group discussion | Evaluator / iteration cap | Small | — | Groups help GPT-4, hurt GPT-3.5; conformity, destructive behavior |
| Moltbook | Open broadcast network | Feeds, hubs | Posts/comments | — | ~1M posts | — | Form without function; hubs dominate |

## 5. What survived contact with frontier models

**Survived.**

1. **A shared, durable work ledger that agents pull from.**
   - Examples: test failures (C compiler), Beads (Gas Town→Wheelhouse), the task list (agent
     teams), planner-emitted tasks (Cursor), the JSON feature list (long-running harness).
   - This is the common core of every working run with Opus 4.6+ and GPT-5.x.
2. **Workers that don't coordinate with each other.**
   - Cursor's workers, the C compiler's agents and Wheelhouse's fleet exchange almost nothing
     peer-to-peer.
   - Coordination lives in the ledger, git and the merge queue.
3. **Recursive or continuous planning by a dedicated role.**
   - Examples: Cursor's planners and sub-planners, Yegge's design beads written by Fable, Cognition's
     manager.
   - Flat swarms without it went risk-averse (Cursor) or built poor games (Anthropic red team).
4. **Clean-context review or verification gates.** Examples: Fable review per bead, Cognition's
   Devin Review, Cursor's judge, the red team's arbiter, the near-perfect test oracle in the C
   compiler.
5. **Deterministic watchers instead of an attentive manager.** Wheelhouse's about 45 crons;
   agent-team hooks (`TeammateIdle`, `TaskCompleted`).
6. **Merge queues, with workers resolving their own conflicts.** Cursor removed the integrator.
   Yegge moved from bisection to megabatches under load.
7. **Shared forums for *exploration*.** Breadth went up 12× in vulnerability hunting. The
   decentralized mesh also did best on web navigation in the Google/MIT study.

**Did not survive.**

1. Flat self-claiming through a shared state file with locks or OCC at about 20 agents (Cursor).
2. Unstructured negotiation swarms for *building* (Cognition; Anthropic red team).
3. Role-play chat chains as the main artifact channel (ChatDev, CAMEL). These were replaced by
   structured artifacts and git.
4. A single orchestrator that relays everything. Yegge is building agent "meetings" to remove
   himself as relay. Anthropic's research system notes synchronous-wait blocking. This is the
   problem /swarm exists to fix.
5. Gas Town itself, on Opus 4.7. Harnesses tuned to one model's quirks broke on the next model.

## 6. Implications for /swarm

These are my recommendations. I'm flagging them because the user may be away and these are
judgment calls.

1. **Separate "flat communication" from "flat work allocation".** Make the swarm flat in who may
   talk to whom and who may create or split work. Don't make work allocation a negotiation.
   Give it a **durable ledger** that every agent reads, files into and claims from: git-backed,
   with dependencies, like Beads or the agent-teams task list. Messages are for questions and
   discoveries, not for "who's doing X".
2. **Claim through git, not a lock file on local disk.** The C compiler's push-a-claim-file
   pattern worked at 16 agents because a rejected push arbitrates. Cursor's shared-file locks
   collapsed at 20. Use atomic claim commits (or `gh` issue assignment) with leases that expire,
   so a dead agent doesn't hold work.
3. **Keep a planner role even without a manager.**
   - Let any agent file tasks, but have one or more **planner** agents (Opus/Fable) whose job is
     to turn goals into beads and spawn sub-planners per area, like Cursor and Wheelhouse.
   - The **communicator** talks to the human and writes goals into the ledger. It doesn't track
     lanes.
   - This directly removes /orchestrate's bottleneck without going fully flat.
4. **Give each task one owner end-to-end, with a single writer per area** (Cognition; agent-team
   docs on same-file edits). Ownership counters the OCC risk-aversion Cursor saw: "no agent took
   responsibility for hard problems".
5. **Replace orchestrator attention with watchers.** Cron or hook scripts watch CI, PRs, idle
   panes and stuck claims, then message the *owning* agent directly ("crons watch, models act").
   This is the cheapest big win and doesn't depend on the comms shape.
6. **Reviews by a fresh-context peer, and a merge queue.** The owner opens the PR, and a reviewer
   peer with no shared history reviews it. A queue merges, and the owner fixes its own conflicts.
   Don't create an integrator role (Cursor removed it).
7. **Comms shapes, ranked by evidence for experiments.**
   - **(a) Direct messages plus a ledger.** Agent teams and Wheelhouse use this. Safest default.
   - **(b) Topic channels or a forum** for discoveries ("X's API changed", "flaky test Y").
     Anthropic's forum worked for exploration but did not prevent building conflicts. Keep it
     subscribe-by-topic, as in MetaGPT's pub-sub, not all-to-all: Moltbook and AutoGen show
     broadcast drifts to hubs and noise.
   - **(c) Selected-set broadcast.** Useful for "everyone touching module M". Agent teams doesn't
     have it ("one message per recipient"), so /swarm would need to build it.
   - **(d) Rooms/breakout rooms** (one room at a time, moving between rooms). **I found no prior
     art run at scale for coding.** Closest are Smallville's spatial proximity [G35] and
     Yegge's *planned* meetings. Treat it as the novel experiment, time-boxed, with a scribe who
     writes outcomes to the ledger.
8. **Design against conformity and unawareness.**
   - Same-model agents converge (18 of 30 picked the same branch name). Pre-assign names and
     areas, and vary the model or prompt per planner.
   - Agents unaware of each other sabotaged one another. Every agent must see the roster and
     ledger at startup.
   - Treat peer messages as untrusted. Claude Code's classifier already does this.
9. **Make endings explicit.** Per-cycle judge plus fresh restarts (Cursor); task-level
   "done = tests pass + review approved" (C compiler, Wheelhouse). MAST's "unaware of
   termination" (12.4%) and premature "done" are the common failures.
10. **Budget honestly.** Measured costs:
    - About $20k for 2 weeks of 16 Opus agents.
    - About 27M tokens for a 45-agent run.
    - About $87k/month API-equivalent for 40+ agents running 24/7.

    Token usage scales linearly with agents (agent-teams docs). Start the swarm at 5–8 agents
    on separable work and grow only where the ledger shows a backlog. MacNet saturates around 100;
    Cursor's flat design topped out at about 2–3 effective agents.
11. **Expect to retune per model.** Gas Town broke on Opus 4.7; Cursor found GPT-5.2 and Opus 4.5
    differ in persistence. Keep model choices per role in one config, and re-run a smoke wave on
    every model change.

## Sources

Primary, frontier-era:
- Anthropic, Building a C compiler with parallel Claudes — https://www.anthropic.com/engineering/building-c-compiler
- Anthropic, How we built our multi-agent research system — https://www.anthropic.com/engineering/multi-agent-research-system
- Anthropic, Effective harnesses for long-running agents — https://www.anthropic.com/engineering/effective-harnesses-for-long-running-agents
- Anthropic Frontier Red Team, multi-agent systems research — https://www.anthropic.com/research/multiagent-systems
- Claude Code docs, agent teams — https://code.claude.com/docs/en/agent-teams
- Cursor, Scaling long-running autonomous coding — https://cursor.com/blog/scaling-agents
- Cursor, Expanding our long-running agents research preview — https://cursor.com/blog/long-running-agents
- Cognition, Multi-Agents: What's Actually Working — https://cognition.com/blog/multi-agents-working
- Gas Town README — https://github.com/steveyegge/gastown
- Yegge, Welcome to Gas City (listing) — https://yegge-ai.pages.dev/listings/welcome-to-gas-city
- Yegge, The Shape of Things to Come — https://yegge.ai/essays/the-shape-of-things-to-come/
- Yegge, Welcome to Gas Town (403, unverified) — https://steve-yegge.medium.com/welcome-to-gas-town-4f25ee16dd04
- Kim et al., Towards a Science of Scaling Agent Systems — https://arxiv.org/abs/2512.08296 ; https://research.google/blog/towards-a-science-of-scaling-agent-systems-when-and-why-agent-systems-work/
- SwarmResearch — https://arxiv.org/html/2607.02807v1
- Moonshot, Kimi K2.5 — https://www.kimi.com/blog/kimi-k2-5
- Moltbook analyses — https://arxiv.org/html/2602.12634 ; https://arxiv.org/pdf/2605.27349

Frameworks:
- OpenAI Swarm — https://github.com/openai/swarm
- OpenAI Agents SDK handoffs / multi-agent — https://openai.github.io/openai-agents-python/handoffs/ ; https://openai.github.io/openai-agents-python/multi_agent/
- LangGraph Swarm — https://github.com/langchain-ai/langgraph-swarm-py
- LangChain, Benchmarking multi-agent architectures — https://www.langchain.com/blog/benchmarking-multi-agent-architectures
- AutoGen SelectorGroupChat — https://microsoft.github.io/autogen/stable/user-guide/agentchat-user-guide/selector-group-chat.html
- AutoGen repo (archived) — https://github.com/microsoft/autogen
- Magentic-One — https://arxiv.org/abs/2411.04468

Research, 2023–2025:
- CAMEL — https://arxiv.org/abs/2303.17760 ; OASIS — https://arxiv.org/abs/2411.11581 ; OWL — https://arxiv.org/abs/2505.23885
- MetaGPT — https://arxiv.org/abs/2308.00352
- ChatDev — https://arxiv.org/abs/2307.07924 ; MacNet — https://arxiv.org/abs/2406.07155
- Generative Agents — https://arxiv.org/abs/2304.03442
- AgentVerse — https://arxiv.org/abs/2308.10848
- MAST, Why Do Multi-Agent LLM Systems Fail? — https://arxiv.org/abs/2503.13657

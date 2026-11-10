# sw-roles: agents that choose their own role

Plan, 2026-11-09, against `swarm/` at 0455397. No code here; §8 is the build
split. Read with [DESIGN.md](../DESIGN.md) (decisions 1, 6, 7),
[sw-lifecycle.md](sw-lifecycle.md) §4.1 and [sw-ownership.md](sw-ownership.md) §4.

## 1. The request

An agent may be an implementer, an orchestrator, a reviewer, a designer, a
planner or anything else, and may switch as the work changes. The CLI and
watchd guarantee four things and impose no flow:

1. agents are tracked, so the user sees each one's status and role;
2. tasks are tracked when agents choose to take them;
3. messages arrive, and spawned agents are hooked into the swarm;
4. agents are nudged to keep working, or to clean up and end.

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

## 7. Deleted or simplified

- `is_comms`' name-suffix rule and the lifecycle exemption for the
  communicator (one general rule replaces a special case).
- `ctx_advice`'s communicator branch becomes the stayer branch.
- DESIGN's "no roles" wording in three places becomes one decision.
- The panel's "comms not counted, shown apart" explanation: it is a stayer
  with a role like any other; its own row can stay.

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
7. **Spawn information (independent).** The live/launched/memory line on
   `swarm spawn`; the refusal only if the user says yes to question 1.

After 2 lands the request is met for agents; 3-7 are nudges, cleanup and views.

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

Questions:

1. Should the user's agent count bind agents' own spawns? Recommended: yes,
   one number in `meta` that `swarm spawn` refuses past, naming the
   communicator as who can raise it. It is the user's budget, not contention
   between agents, so decision 6 doesn't cover it. The alternative is the
   information line alone.
2. Is PR 4 wanted now? It deletes a special case but touches the one agent
   whose wrongful end hurts most.
3. `stay` as the word (`hold` and `wait` are taken or confusable)?

# Swarm panel redesign (board #39)

Status: **design, waiting for approval.** The shots below are a working prototype in this branch
(`ll-ui/39`), drawn by a private Herdr from a made-up swarm (`demo.lua`). The installed panel is untouched.

Before, for comparison: [the current first screen](shots/redesign/before-home-520.png).

## 1. What goes first, and why

The panel is glanced at, not read. A glance should answer three questions, in this order:

| # | Question | On Home | Why it ranks here |
|---|---|---|---|
| 1 | Does anything need me? | **Needs you**: each open question in full, a red main, a hung agent, a machine out of memory. One calm line when there is nothing. | It is the only part that costs the swarm time while you don't look. |
| 2 | Who is running, and on what? | **Agents**: one row each: status dot, name, its task (or what it waits for), state. | It tells you the swarm is alive and what to expect next. |
| 3 | How much is left? | **Tasks**: a done bar, then the tasks still open, most urgent first; links to done and dropped. | It is the progress answer; details are one click away. |

Below those, two things you act on rather than read: **Staffing** (the two numbers, with − and +) and
**More** (Activity, System). The **Away** switch is in the header of every screen.

Moved off the first screen, to the screen where it is useful:

| Was on the first screen | Now |
|---|---|
| Model, cache state, context bar, last event, role chip per agent | The agent's screen. Home keeps only a warning chip (hung, no waiter, context full). |
| Header chips (live, working, claimed, blocked, done counts) | Gone: the Agents and Tasks section titles carry the two counts that matter. |
| Board card with five state counts and "latest done" | Tasks list on Home; the Board screen for everything. |
| Activity feed | More › Activity (Home shows its latest line). |
| Machine footer, CI runs, PRs, locks, command cost, memory per agent | More › System. A problem there surfaces in Needs you. |
| Five tabs | No tabs. Home, and screens that open from it with a back arrow. |

![Home, 520px](shots/redesign/home-520.png)

From 760px Home is two columns; in light themes it uses the same theme colors:

![Home, 860px](shots/redesign/home-860.png)
![Home, 420px, light](shots/redesign/home-420-light.png)

## 2. Screens

```
Home ─┬─ a Needs-you item ──► the task, the agent, or More › System
      ├─ an agent row ──────► Agent
      ├─ "All, N ended ›" ──► Agents (running, communicator, ended) ──► Agent
      ├─ a task row ────────► Task
      ├─ "Board ›" / "N done ›" / "N dropped ›" ──► Board (Active | Done | Dropped) ──► Task
      └─ More ──────────────► Activity (Summary | Full log, filters) | System
Task  ──► its owner (Agent), tasks it waits on or holds back (Task), its PR (browser)
Agent ──► its task and finished tasks (Task), its terminal (Herdr focus), its PR (browser)
```

Every screen below Home has `‹` in the header; screens stack, so back returns where you came from.

**Task.** State, title, actions; the question when it waits on you; owner and lease, who added it,
what it waits on and holds back, time queued/worked/blocked, claims and releases, model and base,
evidence with PR, commit and CI result; the description (markdown); messages that name it; its history.

![Task waiting on you](shots/redesign/task-blocked-520.png)
![Done task](shots/redesign/task-done-520.png)
![Task, light](shots/redesign/task-blocked-420-light.png)

**Agent.** State, role, actions; a hung/no-waiter warning in words; its task; what it waits for,
model, context against the 350k and 550k marks, cache, branch, PR; files it is editing; messages;
tasks it finished; latest events. Ended agents open the same screen, without actions.

![Agent](shots/redesign/agent-520.png)
![Hung agent, light](shots/redesign/agent-hung-420-light.png)

**Agents** and **Board** are the past-items screens: ended agents, done and dropped tasks.

![Agents](shots/redesign/agents-520.png)
![Board](shots/redesign/board-520.png)
![Board, done](shots/redesign/board-done-520.png)

**More** keeps today's Activity and System tabs whole. In the build they get the new type scale and
spacing; their content does not change.

![Activity](shots/redesign/more-activity-520.png)
![System](shots/redesign/more-system-860.png)

## 3. Actions

Every action runs the `swarm` CLI; the panel never writes the db. What the command prints, or the text
of its refusal, shows in a bar at the top of the screen until dismissed.

| Control | Where | Command | Confirmation |
|---|---|---|---|
| Away switch | header, every screen | `swarm away` / `swarm away --back` | none (undo is one click) |
| Auto-spawn to − / + | Home › Staffing, System | `swarm limits --min N` | none |
| Max − / + | Home › Staffing, System | `swarm limits --max N` | none |
| Release task… | Task, while claimed or blocked | `swarm task release N` | "Release #N from ox-1?" |
| End agent… | Agent, while live | `swarm end NAME` | "End ox-3?" |
| End anyway… | the refusal bar, after `end` refused | `swarm end NAME --force` | "End ox-3 anyway?" (a second one) |
| Open terminal ↗ | Agent, Task | Herdr `agent.focus` | none |
| PR #N ↗ | Task, Agent | `gh pr view N --web` | none |

"Kill" is `End anyway`: `swarm end` first runs its checks (working, holds a task or lock, a background
job, work not on its base) and says which one failed; only then is the forced end offered, behind its
own confirmation. Confirmations use Herdr's own confirm dialog (Enter confirms, Esc cancels).

![End confirmation](shots/redesign/agent-end-confirm-520.png)
![Release confirmation](shots/redesign/task-release-confirm-520.png)
![A refusal](shots/redesign/agent-end-refused-520.png)

### Who the panel acts as

The CLI needs a name, and today `end` is the communicator's alone and `task release` the owner's alone
(the refusal in the shot above is that rule). Proposal: the panel runs as **`human`**, a reserved name
that `limits` already logs when no agent is set. The CLI gives `human` the communicator's rights, and:

- `swarm end` accepts `human`.
- `swarm task release N` accepts `human` and the communicator for a task someone else holds (today only
  `drop` and `unblock` do). The ex-owner gets an urgent message: "the user released #N: stop work on it".
- Events log `human` as the actor, so Activity shows "you" did it.

## 4. Away

Swarm has no away today. Proposal:

```
swarm away [note]     # "I'm gone": sets the flag, logs an `away` event
swarm away --back     # clears it, prints what waits and what happened meanwhile
```

While away:

1. **Questions queue instead of pinging.** `swarm task block` still records the question and the task
   still shows under Needs you. watchd does not send the communicator its urgent "X is blocked on #N"
   message, and `task block` tells the agent: "the user is away; park this and take work that doesn't
   need the answer". A prompt in an agent's terminal is handled the same way.
2. **The communicator is told once**, and reminded by its nudge on `read`/`wait`/`board`: "the user is
   away since 12:25: don't ask them; decide what is yours to decide, queue the rest".
3. **Work continues.** Auto-spawn keeps staffing up to your number, the max still caps, a red main
   still becomes a task. Being away changes who gets asked, not how much runs.
4. **On return** (`--back`, or the switch): one urgent message to the communicator, "the user is back:
   N questions wait", and the command's output (also a card on Home until dismissed) lists the
   questions oldest first, tasks finished and PRs merged meanwhile, main's CI state, agents that ended or hung.

Not proposed: answering for you, going away by itself after idle time, or changing the staffing numbers.

![Away](shots/redesign/home-away-520.png)

Cost: rule 1 changes a transition `swarm/model` covers (a block reaching the communicator), so the
model and its replay traces are updated with it. `away`, `--back` and the new rights get CLI tests.

## 5. Look

- One type scale: 16 a screen's title, 14 the header, 12.5 rows, 11 meta. No all-caps labels on the new screens.
- 16px gutters, 10px between sections. Rows sit in one bordered card with hairlines between them,
  instead of a bordered card per row.
- Color only where it means something: the status dot, Needs you (the theme's `blocked`), amber warnings
  (`ansi3`), green done (`ansi2`), the Away switch (`accent`). Everything else is foreground/muted/dim.
- Motion is native: a screen slides in 20px over 200 ms, the working dot pulses, the Away knob and context
  bar ease. No redraw timers; the two data timers are the old ones.
- Content is capped at 720px and centered on the detail screens.

## 6. What the prototype already does, and what the build adds

Real now: every screen and its navigation, the limit steppers, the confirm dialogs, the refusal bar,
`swarm state --json --task N` (body, events, messages of one task), a bare `swarm away` flag that the
switch toggles.

Build, after approval:

1. **CLI** (one board task): `human` rights for `end` and `task release`, the message to the ex-owner,
   away's four rules, `--back`'s digest, tests, `swarm/model` for rule 1.
2. **Panel** (one board task): the "while you were away" card, Activity and System in the new scale,
   delete the old tabs' leftover code, shots of every screen at 420/520/860 in dark and light, actions
   exercised against a scratch db, `SKILL.md`, `install.sh` check, then merge.

## 7. Questions for you

1. **Away**: are the four rules right? In particular rule 3 (work continues at your numbers).
2. **Answer from the panel** (not asked for): a text field on a waiting task that runs
   `swarm task unblock N --answer "…"`. It would make Needs you fully actionable here. Add it?
3. **Acting as `human`** with the communicator's rights: fine, or should the panel act as the communicator?
4. Anything on Home you want back, or gone?

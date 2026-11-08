# Task dependencies as a DAG: worth it, and how

Task #59, 2026-11-08. The question: should a task wait on more than one task, and should the
Herdr Swarm panel show the dependency graph?

## Verdict

- **Several dependencies per task: build it, smaller than proposed.** A `deps` list column
  replaces the `task.after` column. No new table is needed. (An earlier draft kept `after` as a
  compat pointer for old watchds; the user chose to delete it.)
- **A graph view in the panel: don't build it.** Show the DAG in the Board tab's rows instead:
  split open tasks into *ready* and *waiting*, and give each row its "after" and "blocks" lists.
  The graphs are too small and shallow for a node-link view to show anything a list doesn't.

## Evidence: how the three swarms used `--after`

Counted from the three `swarm.db`s on this machine (this repo and two others), 291 tasks in all:

| | count |
|---|---|
| tasks with `--after` | 31 (11%) |
| real second dependency written as prose in the body | 3 |
| largest dependency graph in one swarm | about 12 tasks with deps, depth ≤ 4 |
| graph shapes | chains (1→2→3) and fan-outs (one task, then 3–5 that wait on it) |

The prose cases are real failures waiting to happen. One said "if X isn't there yet, wait for
task #20" on a task whose `--after` named another task. One said "do it after #12 and #14 and the
lifecycle PR merge". One said "closes #88 when the other #88 tasks are done (check the board)".
Nothing enforces prose: `claim` lets the agent start, and watchd auto-spawns the task as soon as
its one `after` is done. That breaks principle 4 (rules beat negotiation). A second dependency
belongs on the board as data, where `pool()`, `claim` and auto-spawn already enforce the first.

The graphs are small: at most about a dozen edges per swarm, and most are already done when
anyone looks. A node-link drawing in a side panel (often under 520 px wide) would show a few
short chains in a lot of empty space, or a tangle at a fan-out. Either way it repeats what the
rows say.

## Prior art (from memory of these tools, not re-checked for this note)

- **Claude Code agent teams:** each task has `blockedBy` and `blocks` lists, shown as lists. A
  blocked task can't be claimed.
- **Beads (Yegge's issue tracker for agents):** `bd dep add`, plus `bd ready` for the startable
  work, and `bd dep tree` prints the graph as indented text.
- **Linear and GitHub issues:** "blocked by" and "blocking" relations, shown as an icon on the
  row and lists on the item. There is no graph view in the everyday list.
- **Taskwarrior:** a `depends:` list, and `ready`, `blocked` and `blocking` reports.

They all store a list per item, enforce "ready = every dependency done", and show lists with a
*ready* view. Graph drawings are rare, and when they exist they are add-ons. The question people
ask of a board is "what can start now, and what is this waiting on?". Lists answer that.

## Design (#60): the CLI and store

**Store.** `task.deps text` holds the ids the task waits on, comma-separated, in the order
given. It is the only store: the old `task.after` column (one id) is gone. `connect()` migrates
an old db once, in one transaction: `update task set deps=after where deps is null and after is
not null`, then `alter table task drop column after` (sqlite 3.35+).

A task is startable when every dependency is done. `pool()`, `claim`, `reserve()`, `swarm
board`, `task show` and `state --json` all read `deps`. An earlier draft kept `after` as a
pointer to the dependency waited on now, so a watchd on old code stayed correct. The user chose
to delete the old way instead: no other swarm needs it, and the one old watchd restarts when
this lands.

**CLI.**

- `swarm task add "<title>" --after 3,5`: `--after` takes a comma list (`--after 3` still
  works). Every id must exist. A new task can't be in a cycle, so no cycle check is needed here.
- `swarm task after <id> <list>` sets a task's dependencies afterwards; an empty list clears them.
  It refuses a cycle by walking `deps` from each new dependency, and the refusal names the
  path ("#5 → #9 → #7 → #5"). It refuses a task that isn't `open`. The command is needed because
  the board has no edit command, and today the only way to add a dependency later is to drop the
  task and add it again.
- `swarm board`: `after #3, #5` lists the dependencies that aren't done. A dropped one shows as
  `#3 (dropped)`.
- `swarm task show`: an `after:` line with every dependency and its state, and a `blocks:` line
  with the open tasks that wait on this one.
- `swarm task drop <id>`: if open tasks wait on it, print them ("#7 waits on #3: drop it too, or
  `swarm task after 7 …`"). This is information, not a rule. A dependency that was dropped still
  holds its dependants back, because nobody decided the work isn't needed.

Tests in `swarm/test_swarm.py`:

- the migration (`after` copied into `deps`, then the column dropped);
- `--after` with a list;
- `pool()`, `claim` and `reserve()` holding a task until its last dependency is done;
- `task after` refusing a cycle and refusing a task that isn't open;
- the board and show lines;
- the warning on `drop`.

## Design (#61): the panel's Board tab

No graph view. In `swarm/herdr/mods/swarm/main.js`'s `boardRows`:

- Split `open` into two groups: **ready** (open and not `waiting`) and **waiting**. Ready comes
  first; waiting stays dimmed as now.
- A waiting row's subline reads `after #3, #5` (the dependencies that aren't done). It replaces
  today's `after #N`.
- A row that open tasks wait on gets `blocks #7, #9` in its subline, on claimed and blocked rows
  too. That shows the user what a stuck task holds up.
- Clicking `#N` in either list jumps to that row.

`state --json` gives each task `deps` and the open ids that wait on it (`blocks`), so the panel
doesn't recompute the graph. Check it with `herdr-app` on a real board, and put a screenshot in
the PR.

## Not doing

- **A dependency table.** One `deps` column is enough at this size.
- **Dependencies on PRs or outside events.** "After PR #12 merges" is a task's `done`, since a
  task is done when its work is on main.
- **Treating a dropped dependency as met.** The board shows it, and the user decides.
- **A text tree in `swarm board`.** The lists say the same in less space, and agents read
  `task show`.

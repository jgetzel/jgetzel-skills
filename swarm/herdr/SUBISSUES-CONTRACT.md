# Sub-issues: the CLI contract (lane 1, shipped)

Sub-issues are a goal hierarchy: `task.parent` (one parent per task, null = top level). It is separate from provenance
(`task.parents`, the tasks the filer held when filing), which stays as is and is shown as "Filed from".
Open = state category not completed/cancelled (backlog, ready, in_progress, needs_input, in_review). Closed = completed,
cancelled, duplicate. DB_VERSION is 3 (an older binary refuses to write a v3 db).

Rules the UI may rely on
- A task with any open sub-issue is a container: auto-spawn and offered work never staff it. The swarms view's `next`
  and `ready` leave it out. `swarm queue` shows why: "has open sub-issues".
- A parent is never completed automatically. When its last open descendant closes, a Needs-you item
  "sub-issues-done" appears for it; it goes once the parent is closed.
- progress = over ALL descendant leaves at any depth (leaf = task with no children); total excludes cancelled and
  duplicate leaves; done = completed leaves. A task with no children has progress null.
- Completing or cancelling a task with open sub-issues is refused unless `--children cancel|keep`.

## CLI

```
swarm task add <title> ... --parent N        file as a sub-issue of open task N (refused: missing, closed)
swarm task parent <id> <N>                   set (refused: missing task, self, cycle, N missing or closed)
swarm task parent <id> --none                clear
swarm task done <id> --evidence E [--children cancel|keep]
swarm task drop <id> [--children cancel|keep] [--duplicate-of M] [--note T]
swarm board --by parent                      text tree; children indented 2 spaces per level; parent line ends "[d/t done]"
```
`--children cancel` cancels every open descendant too (each as `task drop` would; refused if one is another agent's
claimed task and you are not the communicator/user); `--children keep` closes the task and leaves the open
descendants open (parent unchanged). `task parent` has the same permission as `task label` (no ownership needed).
The event kind `task-parent` ("#id parent #N" / "#id parent none") is in the task's activity.

## `swarm task show <id> --json` (new keys; the rest unchanged)

```json
{"id": 7, "parent": 3, "parent_title": "Ship the thing",
 "ancestors": [{"id": 1, "title": "Goal", "state": "ready"}, {"id": 3, "title": "Ship the thing", "state": "in_progress"}],
 "sub_issues": [{"id": 9, "title": "Part A", "state": "completed", "owner": "a1"},
                {"id": 10, "title": "Part B", "state": "ready", "owner": null}],
 "progress": {"done": 1, "total": 2}}
```
`parent`/`parent_title` are null at the top level; `ancestors` is root-first (the direct parent last), empty at the top
level; `sub_issues` are the direct children in id order ([] when none); `progress` is null with no children.
`owner` is the task's assignee column.

Text: `Parent: #3 Ship the thing (in_progress)`, then `Sub-issues: 1/2 done` with one line per child
(`  #9 completed Part A`); the provenance line is now `Filed from #4, #5 by <agent>`.

## `swarm state --json` task objects (every view that emits tasks)

Full/board/agent views (Cmd/State.lean taskJson) and the machine-wide `tasks` of `--view swarms` each gain:
```json
{"id": 3, "parent": 1, "progress": {"done": 1, "total": 2}, "parents": [4, 5]}
```
`parent`: int|null. `progress`: {done,total}|null (null for a task with no children), computed from the WHOLE db,
so it is right for a parent whose completed children are paged out. The existing `parents` key (provenance) is
unchanged. In the swarms view tasks have no `parents` key, as before.

## Needs-you item: kind "sub-issues-done"

An open parent (not completed/cancelled) with at least one child and no open descendant.
```json
{"kind": "sub-issues-done", "task": 3, "title": "Ship the thing", "progress": {"done": 2, "total": 2}}
```
Emitted in `state --json --view summary` `needs`, in each swarm's `needs` of `--view swarms` (a swarm's tasks only), and
in the swarms view's machine-wide top-level `needs`. `progress.total` can be 0 when every leaf was cancelled.
Closing the parent (`task done` or `task drop`) removes it.

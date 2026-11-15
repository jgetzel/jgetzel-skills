# sw-graph-view: the board's tasks as a dependency graph

Board #190. A DAG of the tasks in the rework's swarm view: a node per task, an edge per `--after` dependency
(sw-deps.md's `deps` list). Two scopes: the queue and what it waits on, or the whole board.

sw-deps.md (#59) decided against a graph view: the graphs were small and the Board's rows already say "after #3, #5"
and "blocks #7". The user has since asked for one. What the rows can't show, and the graph does: a chain's depth, a
diamond (one task that two lines of work meet at), and which open task holds the most work back. So this view is for
reading the shape; the rows stay the place for acting on a task.

## Where it lives

A **List | Graph** switch at the head of the Board section, not an eighth section.

- It is the Board's own data and the Board's queue, seen another way; the Board's cards (queue, groups, new task,
  done) stay the place to act, and one switch flips between the two readings of the same tasks.
- The bar keeps seven sections (it is full at 1512 px with Side and Full), and the side view's section menu is
  unchanged: Board there has the same switch.
- The choice is kept in `shared("rw-swarm.view")` (`board: "graph"`, `graph: "queue" | "all"`, `done: true`), so the
  task page's Back returns to the graph, and Expand / Side keep it.

## What is drawn

```
 Board   [List | Graph]    [Queue | All tasks]  [ ] Done too                         7 tasks · 6 edges
┌──────────────────────────────────────────────────────────────────────────────────────────────────────┐
│  ✓ #153 Calendar mod port ───────╮                                                                   │
│                                  ╰──▶ ┃#154 Place calendar in layout ┃──▶ ┃#156 Calendar settings   ┃ │
│                                       ┃ready · Q1 next               ┃    ┃after #154               ┃ │
│                                                                                                      │
│  ┃#160 Store schema        ┃──╮                                                                      │
│  ┃claimed · ll-131         ┃  ├──▶ ┃#162 Migrate the db       ┃──▶ ┃#163 Drop old columns   ┃       │
│  ┃#161 Lua reader          ┃──╯    ┃after #160, #161 · Q2     ┃    ┃after #162              ┃       │
│  ┃waits on you · ll-133    ┃                                                                         │
└──────────────────────────────────────────────────────────────────────────────────────────────────────┘
 No dependencies · 3
  #167 Phone app …   held        #170 Crash safety …   claimed · ll-127      #181 Group done by day   ready
```

- **Layers by depth, left to right.** A node's layer is one past its deepest prerequisite among the drawn nodes
  (longest path), so prerequisites stand left of what waits on them and each column is "can start once the column
  left of it is done". Left to right because titles are wide and depth is short (≤ 4 on every board so far): four
  layers of 232 px fit the full view at 1512 px. In the side view (under 700 px of the view's width) the layers run
  top to bottom instead and nodes are 176 px, so a chain scrolls down, as everything else there does.
- **Order inside a layer:** by queue position, then id; then two barycentre sweeps (a node moves to the mean slot of
  its neighbours in the layer before, then after) so a diamond's two arms sit side by side and edges rarely cross.
- **Edges** go from a prerequisite's right side to its dependant's left side as a cubic curve with an arrowhead,
  drawn with `window.paint_path` on one layer under the nodes. An unmet edge (prerequisite not done) is the muted
  colour; a met one (prerequisite done) is the border colour, so the reader sees which lines still hold work back.
- **Large boards.** Done tasks do not swamp it: a done task is drawn only as the prerequisite of a drawn open task
  (one hop: its own prerequisites are not followed), as a short one-line node with a ✓, since that is what tells the
  reader why a task is startable. **Done too** (All tasks only) adds every done task that has an edge, so finished
  chains show; done tasks with no edge are never drawn, and a dim line counts them ("170 done tasks with no
  dependencies are not drawn: List › Done lists them"). Dropped tasks show as prerequisites only, dashed. The canvas
  is sized to its nodes and scrolls sideways inside the card when it is wider than the view.

## Scopes and tasks with no edges

- **Queue:** the queued tasks (`qpos`), every not-done task they wait on, transitively, and those tasks' done
  prerequisites. With nothing queued: "Nothing queued: auto-spawn staffs by priority" and a link to All tasks.
- **All tasks:** every task that is not done or dropped, and their done prerequisites (and with Done too, every done
  task with an edge).
- **No edges:** a task in scope with no prerequisite and nothing waiting on it is not a graph node; it is in one
  wrapped strip under the graph, **No dependencies · N**, as small cards in the Board's order (waiting on you, in
  progress, ready, held) or, in Queue, in queue order. They are in scope, so they are shown; they are grouped because
  spread through the layers they would read as layer-0 roots of nothing.

## A node

Two lines, 232 x 50 px (176 in the side view), the Board's card look (surface, 1 px border, radius 8):

- Line 1: `#id` dim, then the title, truncated.
- Line 2, the state, coloured as the Board's groups: **ready** (open, not held, every prerequisite done: startable
  now) with a 3 px green bar at the left edge, the one mark of startable; **claimed · owner** muted; **waits on you ·
  owner** coral (blocked: it waits on the user); **held: why** dim; **after #3, #5** dim (the prerequisites not done);
  then the queue position `Q2` at the right, `Q1 next` for the queue's next.
- A done prerequisite: one line, 28 px, `✓ #153 title`, dim. Dropped: the same with a dashed border and `dropped`.
- The task the hover is on lifts its border to the foreground colour.

## A click

A click on any node, or on a card in No dependencies, opens the task page (`openTask`, as a Board row does); its
Back returns to the Board with the graph shown.

## Data

`swarm state --json --view overview` (what the Board reads every 3 s) already sends every not-done task with `deps`,
`undone` (the deps not done), `blocks`, `qpos`, `state`, `owner` and `hold`: enough for the edges between open tasks
and the queue order. Missing: the done prerequisites themselves (overview sends only a few recent done tasks, so a
done dep is an id with no title), and for Done too, the done tasks with edges.

A new view, **`--view graph`**: the header and the tasks, nothing else (no lanes, messages or events), the tasks
being every not-done task plus every task that has a dependency or is one. On this board that is 6 open and 46 with
an edge. While the graph shows, the view polls it in place of overview, at the same rate (`pageKey` "graph", as
Activity and System do). The panel then picks a scope from it; the layout is computed when a read arrives, not per
frame.

## Checking it

`swarm/herdr/graph-demo.sh` inside shot.sh's sandbox, after `--rework real`, gives the ll swarm's board a chain (a
done task, then three open tasks after it), a diamond (one task after two, both after a third), three tasks with no
edges and a queue of four, then opens Board › Graph. Shots of both scopes, the side view, and a click on a node
opening the task page go in swarm/herdr/shots/graph-*.png.

# Herdr window rework: build spec

The design is on the canvas: https://claude.ai/artifact/37GVa1N9A2vRYqzwWNpvJp
(private to the user). Five design rounds are recorded there, with each
decision and who made it. This file says how to build it.

herdr-app and hc are third-party. We build with one personal layout file and
personal mods, and we change the swarm CLI. Nothing here edits the app.

## Rules for every slice

- The new UI is a new personal layout, `layouts/rework.json`, with mods named
  `rw-*`. It sits beside today's `jgetzel` layout. `layout.switch` shows it and
  ctrl-shift-l switches back. Nothing replaces today's layout or the swarm
  panel by default.
- Never reuse a name Herdr ships: shipped layouts and mods are replaced whole
  on every start.
- Install goes through `herdr-mods install` (`swarm/lean/SwarmLean/Herdr/Install.lean`),
  which must learn the new layout and mods.
- Mods have no HTML or CSS. They draw with the kit in `gpui-kit.d.ts`.
- Poll only as often as the data changes. Today's swarm mod is the model:
  3 s while shown and something is due, 30 s while a folder watch is quiet,
  10 s for another machine.

## Where the facts come from

Checked on 2026-11-13 by reading the app's guide (`~/.config/herdr-app/AGENTS.md`),
`herdr.d.ts`, `gpui-kit.d.ts`, the shipped mods and layouts, the app's Settings
source (`frame/settings/main.js`), `hc schema`, `herdr-app commands` and
`swarm state --json`. Nothing was run in the app: no mod was loaded and
`herdr-app check` was not run. "Unchecked" below means read in the docs but
not tried.

| Need | Source | Status |
| --- | --- | --- |
| Whole window from a layout (rail, bar, cards, no status bar) | layout nodes `block`, `row`, `column`, `stack`; root `"titlebar":"none"` with a `window_drag` block; `pane.radius/border/focus/gap` on the tab block | documented |
| Every terminal with space, tab, parent, name, status | `terminals()` (the `hc ls --json` record: `labels["herdr.space"]`, `labels["herdr.tab"]`, `parent`, `name`, `title`, `cwd`), `agents()`, `panes()` | checked in slice 1; `status_ms` is null there, so `rw-rail` stamps change times itself, restamping when `turn` changes (a turn it missed while not shown) and taking a one-pane tab's `changed_at` as the time |
| Status words | `working`, `blocked`, `done`, `idle`. The core also has `error`, and `kind` (permission, question, auth) | documented |
| "Done" clears when you look | the app does it; no mod call clears it | documented |
| A shell's front program | `program` on the terminal follows what runs; `foreground {argv, cwd, name, pid}` in `hc schema` | checked in slice 1: `terminals()` carries `foreground` |
| A shell's last exit status | none | not available |
| Focus and navigation | `focused()`, `pane.focus`, `agent.focus`, `tab.select`, `space.select`, `tab.new {mod, props}`, `pane.split {direction, mod, props}` | documented |
| Overlays | `openOverlay({kind: "dialog" \| "popup" \| "window"})`, `notify()` toasts, `HoverCard`, `Popover`, right-click popup | documented |
| Controls | `Input` with `InputState`, `Checkbox`, `Switch` | documented |
| Drag to reorder | no drag API; shipped mods build it from mouse down, move and up | documented |
| Machines | `machines()` gives name and layout state only; `hc machine ls --json` gives `state` (connecting, connected, needs_login, unreachable), `why`, `since_ms`, `version` | documented |
| Per-user state for a mod | `localStorage` (per mod), `shared()` / `setShared()` (all mods), files under `~/.config/herdr-app` | documented |
| Run a command | `exec(command, args, {cwd, on})`, 30 s limit, 8 MiB, `on: space.machine` for another machine | documented |
| Sound | `playSound("done" \| "blocked" \| file)` | documented |

## Marks

One set, used in rail rows, tab pills, pane headers and the swarm tab. The
mark sits at the right end of the row or pill.

| Mark | Meaning | From |
| --- | --- | --- |
| amber ring, spinning | working | status `working` |
| blue dot | done and unseen; plain agents and communicators only | status `done` |
| coral square | asks you | status `blocked`, core `error`, or the agent's swarm task is blocked on the human |
| gray ring | idle | status `idle`; also a swarm worker whose status is `done` |
| coral hollow square | hung (swarm only) | `swarm state` agent that did not answer the liveness check |
| small bright dot | shell: a program is in front | not an agent, and `program` is not a shell (as the shipped spaces mod infers) |
| small dim dot | shell: at a prompt | `program` is a shell and status is not `working` |
| small coral square | shell: last command failed | not buildable, see the last section |

A folded space shows four counts: asks you, working, done, idle, then its
shells (a terminal glyph), so a fold of shells is never blank. A swarm worker
is never counted as done. Its heading's chevron points right.

## Parts

### The rail (canvas: "The rail, state by state", screens 1 to 5)

Spaces grouped by machine, this computer first. Under each space, its agents
and then its shells, one row each: name, title or task, time, mark. A row
whose terminal has a `parent` in the same space hangs under the parent on a
thin line; a parent that is gone, has no pane, or is in another space leaves
it flat in its own space. A row never repeats its name: an agent whose title is
its name shows its last report, its named tab, or its folder instead. A space's
heading is bold with a fold chevron, its rows hang on a guide line under it,
and spaces sit further apart than rows. Each machine's heading is a divider
line with its icon. A space folds to one line with counts (the chevron or a
click on the shown space). Clicking a row focuses that terminal.

- Data: `spaces()`, `terminals()`, `agents()`, `machines()`. No swarm data for
  a plain space.
- States: space open, folded, selected; row selected; space without tabs.
- Buildable: mod `rw-rail` in a layout block.
- Unchecked: the tree line is drawn from plain elements, not tried.

### Collapsed rail (canvas: rail board, E)

A 64px strip: one tile per space with a two-letter name, the open space
outlined, its agents' marks under it. Hover or focus opens the space's rows
beside the tile.

- Buildable: the same mod at a narrow width, the panel with `HoverCard`.
- Built in slice 4: below 160 px the rail draws tiles; its chevrons resize the sidebar to 64 px and back, sharing
  `sidebar.width` with workspace-chrome. The card opens on hover only: a tile can't take keyboard focus.

### Title bar and tab pills (screen 1)

Space name and machine at the left. Tabs as pills: name, title, mark at the
end. A "Needs you N" button and the palette button at the right. No status
bar; machine load is at the foot of the rail.

- Data: `spaces()`, `panes()`, `agents()`.
- "Needs you" counts every agent with `blocked` or `error` on every machine,
  including hidden ones, plus swarm tasks blocked on the human. It does not
  count shells. It opens a popup list; an item focuses the agent.
- Buildable: mod `rw-bar`, layout root `"titlebar":"none"`. On Linux the mod
  draws the window buttons itself (`window().buttons`).
- Reordering pills by drag has to be built by hand, as the shipped tabs mod does.
- Built in slice 2. Swarm tasks blocked on the human join the count with the swarm block (slice 6), which reads the
  summary view. `window().buttons` is false in shot.sh's sandbox (Xvfb has no window manager), so its shot forces the
  buttons on.

### Panes as cards (screen 1)

Each pane is a rounded card with a header: name, title, state, mark.

- Buildable: `pane.radius`, `border`, `gap` on the tab block and a header mod
  `rw-pane`. One header height for the whole layout.
- Limit: only the layout root's look applies today; a block's own look is
  "coming" in the guide.
- Built in slice 3: the `main` block's pane look (radius 12, gap 10, surface, accent focus, `lone`) with a 38 px
  `rw-pane` header. The header's time is rw-rail's stamp, which the rail shares as `shared("rw-rail.changed")`.

### Swarm block in the rail (rail board C and D, screens 2 to 4)

A space whose folder has a swarm shows a block: one summary line (agents,
tasks left), the communicator first, then the workers with their task number.
Plain agents and shells sit below the block. Past 8 agents, working and idle
workers fold into two count rows; agents that ask you, are hung, or that you
opened stay named.

- Data: `swarm state --json` for the space's folder, run with `exec` as
  today's swarm mod does (`cwd`, and `on` for another machine).
- Buildable: part of `rw-rail`.
- Needs the summary output below to stay cheap at 24 agents.
- Built in slice 6: one `swarm state --json --view summary` per space folder every 5 s; the block shows in the space
  whose id is the board's `space` (else every space on that folder). A row is the agent's terminal (`hc`), its
  sub-terminals under it; an agent with no terminal here still gets a row. "You opened" is an agent you clicked in the
  rail (kept across restarts); "show" lists every worker until "show fewer". rw-bar's Needs you also counts the
  summary's questions (tasks blocked on you) whose agent isn't already asking at a prompt.

### Swarm tab (screen 2)

The overview of one swarm, as the first tab of its space: Needs you with an
answer field, the agent table, the board, staffing, messages, landing.

- A terminal cannot be drawn inside a mod. So the tab is the communicator's
  tab, with the overview as a mod pane split beside the communicator's
  terminal (`pane.split {direction, mod: "rw-swarm"}`).
- Data: `swarm state --json`; the answer runs `swarm task unblock N --answer`;
  PRs from `gh pr list` at most once a minute, as today.
- Agent rows show the task title, not the terminal's last line.
- Buildable. Unchecked: that a mod pane split into the communicator's tab
  survives a restart in the right place.

### An agent needs you (screen 3)

The agent's tab: its terminal, the question above it with an answer field,
and a context card (task, why watchd keeps it, context size, files, PR).

- A pane header cannot be taller for one pane. The question is a mod pane
  split above the terminal (`pane.split {direction: "down" ...}` from the
  question pane's side), closed when answered.
- Buildable: mod `rw-question`. Unchecked: how the split behaves when the
  agent's tab already has splits.

### Large swarm (screen 4)

The agent table grouped by state (ask you, hung, working, idle), a filter
field, the board as numbers and next tasks. Ended agents are one line with a
count; opening it lists them read-only.

- Pills show only the agents you opened. A mod can skip tabs when drawing,
  but next-tab keys still reach them. `tab.settle` hides a tab properly and
  brings it back when shown or when its agent needs you, which is the wanted
  behaviour.
- Buildable. Unchecked: `tab.settle` on 20 tabs at once.

### Two swarms (screen 5)

An "All swarms" row at the top of the rail once more than one swarm runs: one
column per swarm, Needs you merged, memory split by swarm.

- A tab cannot belong to no space. The view is a child of a layout `stack`
  beside the tab area, shown with `layout.select`.
- Needs two new CLI outputs below: the list of swarms and memory per swarm.

### Machines (canvas: machines board)

A heading per machine in the rail with a menu: rename, hide, update, log in
again, remove. Rename happens in place. An unreachable machine keeps its
spaces, dimmed, without marks, with Retry. A hidden machine is one line at
the foot of the rail with Show. This computer has no menu.

- Data: `hc machine ls --json`.
- Actions: `hc machine rename|update|login|rm` through `exec`, as the app's
  Settings does; add opens the shipped dialog with `mod.open machine-add`.
- Hide is ours: a list in `shared()`, read by the rail and the bar.
- Buildable: part of `rw-rail`.

### Settings (canvas: settings board)

The app's Settings screen belongs to the app and cannot be extended. It
stays reachable with `app.settings`. Ours is a second view, mod `rw-settings`,
opened from the foot of the rail, with the same sections.

Today's Settings, read from its source:

- Look: layout, appearance, dark and light theme, zoom, terminal font and
  size, interface font.
- Keyboard (macOS): Option as Alt.
- Machines: this computer, each machine with update, rename, remove; add.
- Alerts: sounds on or off; the needs-you and finished sounds, each with Play.
- Updates: check, restart to update, what's new; update herdr-core.
- Privacy: usage data on or off, what is sent.
- A "Send feedback" button.

New in ours: hide and show a machine, and controls for six settings that
today exist only in `settings.json`: `font_ligatures`, `minimum_contrast`,
`pane_scrollbars`, `colors`, `clipboard_write`, `core`.

- Writes go to `settings.json` with `writeTextFile`, as the app's screen does.
- Not in ours: sending feedback (the API is the app's own; link to
  `app.feedback`) and the list of keys (open `keys.json`).
- The canvas board lacks the "Send feedback" row. Add it when the board is next touched.

## New swarm CLI output

In swarm-lean, since the CLI is being ported there.

1. `swarm state --json --view summary`: task counts, per live agent only
   `name`, `status`, `task`, `idle_s`, hung or not, and the list of what needs
   the human. No ended agents, events or messages.
   Built in slice 5: `counts`, `agents` (`name`, `hc`, `status`, `task` {id, title}, `idle_s`, `hung`), `space` (meta's Herdr space), `needs` (kinds
   `question`, `prompt`, `hung`, `ci`, `memory`, as the swarm panel's Needs you), `comms`, `active`. `idle_s` is the
   hook's `last_active`, not hc's lookup, so it stays one db read.
2. A list of the swarms on this machine, with repo folder, tag and db path.
   State is per repo today and nothing lists them, so this needs a small
   registry that watchd writes when it starts and clears when it ends.
3. Memory per swarm: the sum over its agents' process trees. Today there is
   only `running[].rss_kb` per command and the machine-wide note.

`swarm who` records context for watchd, so the UI must not poll it.

## Build slices

Each is one PR and usable on its own once the layout is switched to.

1. Layout `rework.json` and `rw-rail` for plain use: spaces by machine,
   agents and shells with marks, tree line, fold with counts, click to focus.
   The rest of the window uses the shipped tabs and pane mods. The installer
   learns the layout and the mod.
2. `rw-bar`: tab pills with the mark at the end, the Needs you button and its
   list, window buttons, no status bar, machine load at the rail's foot.
3. Pane cards and the `rw-pane` header.
4. Collapsed rail with the hover panel.
5. CLI: `--view summary`.
6. Swarm block in the rail, on the summary.
7. Swarm tab: `rw-swarm` beside the communicator's terminal.
8. Agent needs you: `rw-question` and the context card.
9. Large swarm: grouped table, filter, settled tabs, the ended list.
10. Machines: headings, menu, rename in place, unreachable, hide.
11. `rw-settings`.
12. CLI: the list of swarms, and memory per swarm.
13. All swarms view.

## Not buildable by us

- The failed-shell mark: nothing reports a shell's last exit status.
- A system notification or dock badge while the window is hidden. A mod can
  play a sound and show a toast inside the window only.
- A taller header on one pane (worked around with a mod pane).
- A terminal drawn inside a mod (worked around with a split).
- A tab that belongs to no space (worked around with a layout stack).
- Changing or extending the app's own Settings screen (ours is separate).
- Clearing "done" from a mod. The app clears it when you look, which is what
  the design wants.

## Still unchecked

- Everything marked unchecked above; of the mods here only `rw-rail`, `rw-bar` and `rw-pane` have been run.
- Cost of `exec` polling for several swarms at once.
- Whether `layout.switch` back and forth keeps each layout's pane state; the
  guide says switching starts the layout's mods fresh.

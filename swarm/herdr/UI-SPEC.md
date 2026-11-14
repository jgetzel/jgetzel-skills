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

## How to check

Shoot the rework in shot.sh's sandbox with the real preset, never the person's window:
`swarm/herdr/shot.sh --rework real out.png` (`--before CMD` then clicks or reads in it). Real is about the user's
window: ten spaces and 15 agents on this computer, two swarms made as `swarm spawn` makes them (a joined
communicator, a watchd terminal with no pane, workers that are children of the communicator, of watchd or of an ended
terminal, one asking, one hung, four ended), the spaces' folders off as in the user's window, a second machine with
spaces of the same names and an unreachable third. `--rework large` is the same with a swarm of 24 live and 110
ended; `--rework small` and rail-demo.sh's flags are the first demo, kept for the older shots. Compare the shot with
the canvas board for what you changed. Shots: `shots/real-preset.png`, `shots/large-preset.png`;
`shots/real-preset-pre175.png` is real on the commit before #175's fix, with no swarm block, as the user saw it.

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
- Look D (board #177): a swarm agent's header reads its name and task; the communicator's "Communicator  ll-comms ·
  your channel to the swarm" with the Away switch at its right. The swarm tab's and Needs you's panes draw cards on
  the ground: their header is empty ground. The pane look is one for every pane, so their frame's border stays; the
  pills read a swarm agent's name and "Communicator"; the bar's subtitle for a swarm's space is "This computer · main
  green" from the summary's `ci`; a hung swarm agent is a toast at the rail's foot with what it holds, Nudge and Open.

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
- Built in slice 7: the rail's swarm heading opens it. It splits `rw-swarm` (props `{folder, machine}`) right of the
  communicator's pane, swaps the two so the overview is on the left as drawn (splits only go right or down), and moves
  that tab first; a second click focuses it. With no communicator pane in the window it is a tab of its own. The pill
  of that tab reads "Swarm · N agents" with the diamond. Data: `swarm state --json --view overview`, polled as the swarm
  mod does (3 s while the db folder changes, 30 s quiet, 10 s remote); PRs from `gh pr list --state all --limit 4` once
  a minute. Needs you lists questions with an answer field, agents stopped at a prompt and hung agents, each with Open
  its terminal. Board shows the tasks left (8, then a count), staffing (auto-spawn, max) and New task. Messages are
  the latest three. The Done and Dropped links, the Activity link and Landing's files-not-on-main line are left out:
  the rework has no screen for them yet. Look D (board #177): Done and Dropped links in the board's heading list the
  newest of those tasks in the board's place (`--view board`, read on click); the Away switch moved to the communicator's
  pane header and stays here only while the communicator has no pane in the window.

### An agent needs you (screen 3)

The agent's tab: its terminal, the question above it with an answer field,
and a context card (task, why watchd keeps it, context size, files, PR).

- A pane header cannot be taller for one pane. The question is a mod pane
  split above the terminal (`pane.split {direction: "down" ...}` from the
  question pane's side), closed when answered.
- Buildable: mod `rw-question`. Unchecked: how the split behaves when the
  agent's tab already has splits.
- Built in slice 8: clicking an agent that asks (its rail row, or Open its terminal in the swarm tab) splits
  `rw-question` (props `{folder, machine, agent}`) down from the agent's pane and swaps the two, so the question is
  above; once per tab. Splits are halves and a pane can't be sized, so the context sits in the same pane under the
  question as a row of cards (task: lease, base, worked, PR; why it is still here: watchd's checks, given only for an
  idle agent; context with the 325k and 400k marks, the last compaction and the cache; the files it edits) rather than
  a column beside the terminal, which would leave the terminal a quarter of the tab. Send answer runs `swarm task
  unblock N --answer`; Let the communicator decide posts the question to the communicator, and the question stays.
  Every `rw-question` pane in the agent's tab closes once its task is no longer blocked, answered here or anywhere.
  The cards' buttons (Open task, Release, Message, Nudge, End agent) are left out.

### Large swarm (screen 4)

The agent table grouped by state (ask you, hung, working, idle), a filter
field, the board as numbers and next tasks. Ended agents are one line with a
count; opening it lists them read-only.

- Pills show only the agents you opened. A mod can skip tabs when drawing,
  but next-tab keys still reach them. `tab.settle` hides a tab properly and
  brings it back when shown or when its agent needs you, which is the wanted
  behaviour.
- Buildable. Unchecked: `tab.settle` on 20 tabs at once.
- Built in slice 9: past 8 workers (the rail block's fold) the swarm tab groups the agents under a filter that also
  narrows the board, adds model and PR columns, and shows the board as counts and the next 5 tasks in auto-spawn's
  order (queue, priority, id; not main-red first). The ended line counts every ended agent; opening it reads
  `state --view agents`, which sends the newest 60. Not drawn: the ended line's "landed / ended by you" split and
  "today" (no field says how an agent ended), Pause, and Landing's counts. The rail puts away (`tab.settle`) each tab
  that holds only folding workers unless it is shown; showing one counts its agent as opened. It brings back a put-away
  tab whose worker asks or is hung, since Herdr does so only for a terminal's own prompt. The bar draws the put-away
  tabs as one "N more" pill where the last of them sits; it shows the swarm tab. 19 tabs settle at once in the shot.

### Two swarms (screen 5)

An "All swarms" row at the top of the rail once more than one swarm runs: one
column per swarm, Needs you merged, memory split by swarm.

- A tab cannot belong to no space. The view is a child of a layout `stack`
  beside the tab area, shown with `layout.select`.
- Needs two new CLI outputs below: the list of swarms and memory per swarm.
- Built in slice 13: `rw-swarms`, the "all-swarms" child of a `view` stack that holds the tab area (`main`). The rail's
  swarms are each space folder's plus those `state --view swarms` lists with no space on this computer; past one, the
  All swarms row heads the rail (how many run, how many of their agents ask you) and shows the view. The view reads
  each swarm's `--view overview` every 5 s while shown: Needs you across swarms (Answer opens the question above the
  agent, slice 8), a column per swarm (tag, folder, main's CI, Communicator, Open space, its agents, board counts, the
  next 3 tasks, the staffing line), and this computer's memory in use split by swarm (`rss_kb`) and everything else.
  Any click that shows a tab (the rail, a pill, Needs you, the view's own buttons) or a change of the shown tab puts the
  tabs back. Not drawn: the bar's swarm nav in place of the pills, and "hpl-4's bench would take it to 92 G" (nothing
  says what a task will need); the collapsed rail has no All swarms tile.

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
- Built in slice 10: the heading's menu is a `Popover`; Remove asks in it. State comes from `hc machine ls --json` every
  15 s. Retry reads it again at once: hc reconnects by itself once the machine answers, and has no command to make it
  try. Log in again runs `hc machine login` in a terminal shown with `terminal.peek` (it needs one to ask a password).
  Hidden machines are in `shared("rw-rail.hidden")`; the bar doesn't read it, since Needs you still counts them and
  nothing else in the bar is per machine. Add a machine stays at the foot, where workspace-chrome already has it.

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
- Built in slice 11: a mod can't import from `frame/`, so the installer copies the app's screen into
  `rw-settings/app.js` (exporting its section list) and `rw-settings` extends it: the same sections and code, plus
  the new rows. Keyboard shows on every system, since it also holds Open keys.json, which opens the file in
  `$VISUAL`/`$EDITOR` in a new tab (a `terminal.peek` didn't stay up from the dialog). `colors` and `core` are typed in
  place and checked first. Hide and Log in again sit on a line under each machine. The rail's foot is `rw-settings`
  with `{footer: true}` in place of workspace-chrome's: Settings opens ours as a dialog; the app's stays on
  `app.settings`. The board's "A failed shell" row is left out (nothing reports a shell's exit status). Each
  install re-copies the app's screen, and stops if the screen no longer has `SECTIONS` or its `Settings` class.

## New swarm CLI output

In swarm-lean, since the CLI is being ported there.

1. `swarm state --json --view summary`: task counts, per live agent only
   `name`, `status`, `task`, `idle_s`, hung or not, and the list of what needs
   the human. No ended agents, events or messages.
   Built in slice 5: `counts`, `agents` (`name`, `hc`, `status`, `task` {id, title}, `idle_s`, `hung`), `space` (meta's Herdr space), `needs` (kinds
   `question`, `prompt`, `hung`, `ci`, `memory`, as the swarm panel's Needs you), `comms`, `active`. `idle_s` is the
   hook's `last_active`, not hc's lookup, so it stays one db read. Look D (board #177) adds `ci` (the latest run on the
   base, {`status`, `conclusion`}, or null) and `away` (true while the user is away).
2. A list of the swarms on this machine, with repo folder, tag and db path.
   State is per repo today and nothing lists them, so this needs a small
   registry that watchd writes when it starts and clears when it ends.
   Built in slice 12: `swarm state --json --view swarms` (from any folder) gives `swarms` [{`db`, `folder`, `tag`,
   `comms`, `pid`, `started`}], by folder. Each is a file in `$XDG_STATE_HOME/swarm/swarms` that a watchd (not
   `--once`) writes when it starts and removes when it exits. A watchd that died without exiting is dropped from the
   list, and its file goes, once its pid is gone.
3. Memory per swarm: the sum over its agents' process trees. Today there is
   only `running[].rss_kb` per command and the machine-wide note.
   Built in slice 12: `rss_kb` in `--view summary`, the live agents' process trees on this machine counted from
   their claude process (as the System view's holders), so the rail's poll of each swarm's summary carries it.

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

# Part II (board #181, 2026-11-14)

Canvas: https://claude.ai/artifact/Htmy5WArT49WUzzPYUntid (private to the user), one board per item. Design only: no
mod was written. "Tested" means run in shot.sh's sandbox or a private headless compositor on herdr-app 0.1.13;
"read" means found in `AGENTS.md`, `herdr.d.ts`, `gpui-kit.d.ts`, `herdr-app commands` or `hc schema` and not tried.
Slices are numbered II.n; each is one PR.

Round 2 (the user's answers, 2026-11-14): screens are a MacBook (assumed 1512 x 982), a Framework at 1800 x 1200 and
a desktop at 2560 x 1440; the swarm view is full width; task and agent detail are pages with a back arrow; tabs live
only in the rail (no pills); no x on swarm tabs; blur is held; all the motion and more, with a switch; one builder,
in the order at the end.

## II.1 Close button on tabs

- Facts (read): `tab.close {id, confirmed}` ends the tab's terminals; Herdr asks only for a space's last tab.
  `pane.close {pane}`. `on_mouse_down("middle")` is in the kit's types. No undo: a closed terminal is ended.
- Rail rows: a plain row draws a x on hover in the mark's place (the row keeps its width); middle click too. It
  closes the tab when the tab has one pane, else that pane. Never on a swarm agent, the communicator or the swarm row.
- Ask first (the shipped `confirm` dialog) when an agent is `working` or `blocked`, when a shell has a program in
  front, and when the tab is the space's last. Otherwise close at once with `confirmed: true`.
- Swarm agents: our own popup menu (Message, Open its page, Nudge, End agent). End runs the plain `swarm end NAME`
  (ends only an idle agent with its work landed); a refusal shows its reason and End anyway (`--force`) as a
  second, confirmed step.
- Slices: II.1a x on rail rows, middle click, confirmation. II.1b the swarm agent menu (after II.3d).

## II.2 Tabs live in the rail

- Decided: no pills. rw-bar draws the space, then nothing until Needs you and the palette button: the shown tab is
  named by its selected rail row and its pane header, so the bar does not repeat it (round 3). The bar stays as title
  bar and drag region. With the swarm view shown it draws the sections
  (II.3); with All swarms, the name only. `PILLS`, the edge pills, the "N more" pill and the pill drag go.
- Rail: a + on a space's heading on hover and a New tab row at the end of the shown space, both opening the shipped
  `new-menu` (`tab.new {space, argv}`); the Calendar row at the foot between Settings and Add machine; a split tab's
  rows joined by a bracket, with the tab's name over it when named; double click renames in place
  (`tab.rename {id, name}`); a `HoverCard` with the full title, folder, branch and state. A large swarm's put-away
  workers are the block's "N working / N idle" rows only.
- Drag to reorder inside a space: `tab.move {id, index}`; the drag is built from press, move (4 px threshold) and
  release, as the shipped `spaces` mod does for spaces; a drop line, rows parting, Escape cancels; a tab moves whole
  and nothing lands inside a bracket; swarm agents and sub-terminals don't drag.
- Round 3: cross-space moves stay out; the drag is animated (II.4: rows part, the dropped row springs).
- Not possible: moving a tab to another space (no command; relabelling its terminals with `hc label` is untried and
  would lose splits and mod panes) and dragging a row into another tab as a split (no command moves a pane).
- Sizes: the rail is 268 px on all three screens (resizable to 480).
- Slices: II.2a bar without pills, the rail's +, New tab row, brackets and Calendar row. II.2b rename in place and
  the full-title card. II.2c drag to reorder.

## II.3 Full swarm information

Inventory (every item of `mods/swarm/main.js`, every field of `swarm state --json`'s seven views, every CLI command,
against the rw-* mods): the old panel's Task, Agent, Activity and System screens and its queue are gone; Home lost the
away digest, the CI / watchd / memory needs, Pause, Queue only, the stay signs and the idle reason. Two bugs:
rw-swarm's own Away box reads `away === true` but `--view overview` sends `{since, note}`; `tree.js` `overOf`/`sumOf`
drop every field they do not list, so a restored item starts by adding its fields there.

Shape: the swarm view is a child of the `view` stack (as All swarms), full width; rw-swarm with a `section` prop.
While it shows, rw-bar draws the sections (Overview, Agents, Board, Activity, Landing, System, History): this is the
bar's swarm nav left open in Part I. Task and agent detail are pages inside the view with a back button that names
where you came from (a section, or the tab you were on); any task number or agent name in any rw-* mod opens them
(`shared("rw-swarm.page")` plus `layout.select`). Sizes: cards in two columns under 1900 px of view width (MacBook,
Framework), three from there (desktop), where Overview's third column adds the latest activity and the landing queue; pages
and the Activity list stop at 1100 px.

- Overview: Needs you with every `needs[]` kind (question with answer field, prompt per II.6, hung with Nudge, `ci`
  with Open run and `gh run rerun --failed`, watchd not running with Restart, `memory`); the Away banner and the
  "While you were away" digest (`back`); agents with `fate.short` and `stay_sign` chips; board counts and next;
  staffing with Pause/Resume and Queue only (`limits --queue-only`); Message the swarm (`swarm post` to the
  communicator, `all`, or one agent, with Urgent); Spawn (`swarm spawn`); the machine line.
- Board: the queue (`qpos`) with "next", why-not, move (`queue add --front/--before/--after`), remove (`queue rm`) and
  add (`queue add`); the four groups; done and dropped (`--view board`) with `work_s` and `done_ctx - claim_ctx`;
  the new-task form with body, after, priority, model, effort, queue, hold.
- Task page (`--task ID`): all the old task screen had, plus `task edit`, `task after`, queue add, `merge_to_green_s`.
- Agent page (`--agent NAME`): all the old agent screen had, plus Compact (`swarm compact`) and its locks.
- Activity (`--view activity`): the old screen, plus a search field.
- Landing: open PRs (`gh pr list`, with agent, checks, review); main's CI runs with re-run; landed today with
  `merge_to_green_s`; branches not on main.
- System (`--view system`): watchd with Restart, machine and pressure, memory by agent, remote jobs, command cost,
  locks (with `since`, `lease_until`), conflicts, memory episodes, refused spawns; rules and limits (needs CLI).
- History: done tasks with time and context spent, ended agents (needs CLI paging past the newest 80 / 60).
- Bench forecast: "what a task will need" is not knowable. Buildable: a running command's past peak (`running[]`
  matched to `cost_top[]`), shown as "peaks at N G" and added to the machine line.

CLI additions (swarm-lean): `rules` and `limits.ctx_nudge / ctx_compact / compact_stayers` in state;
`--view board --before ID` and `--view agents --before TS`; a past peak on each `running[]` row;
`needs[kind=ci].fixer`. Not possible: an agent's cost in money (nothing records it).

Slices: II.3a the two fixes. II.3b full-width view, bar nav, Overview. II.3c task page. II.3d agent page.
II.3e Board. II.3f Away banner and digest. II.3g Activity. II.3h Landing. II.3i System with the forecast.
II.3j Message the swarm and Spawn. II.3k CLI rules and limits, then their card. II.3l CLI paging, then History.
II.3m All swarms links into the sections and shows the same needs.

## II.4 Microanimations

- Facts (tested with a throwaway mod shot every 0.25 s): `.transition(prop, ms | {duration, delay, easing})` and
  `.spring(prop)` animate later changes of `width`, `height`, `left`, `top`, `opacity` natively; `.loop(prop, {from,
  to, period})` pulses; `.frames` and `svg().spin` exist (marks use them). A colour change is instant: no colour,
  scale or rotation of a box. Nothing of the app's own animates: terminals and the tab's content, the app's dialogs,
  toasts, palette, layout show/hide and stack switches, pane splits. A floating block's `peek` drawer slides (read).
  Hover styles apply in one step; a hover highlight as an opacity layer is read, not tested (no pointer in the sandbox).
- Spec, all from those five properties: hover as a highlight layer fading in 90 ms and out 140 ms (read, not seen
  working: the pointer test did not reach the test mod; fall back to instant hover); the rail's selected-row and the
  bar's selected-section highlight slide (`top`/`left` and size, 140 ms); rows coming and going (`height` and
  `opacity`, 160 ms); drag: rows part (`height`, 120 ms), the dropped row springs; pages push in from the right
  24 px (`left`, `opacity`, 160 ms) and back; popups and menus fade in and rise 6 px (120 ms; mount at 0, then set
  the target); folds, cards and the hung toast (`height`, 160 ms); a new "asks" mark pulses a minute and Needs you
  pulses twice when its count rises (`loop`); marks cross-fade on a state change (two stacked, `opacity`, 200 ms);
  meters slide (`width`, 300 ms); rail collapse (`width`, 180 ms); placeholder rows pulse while a swarm is first read.
  "Animations" in rw-settings, on by default; off leaves only the working spinner.
- Slices: II.4a the setting and the rail. II.4b hover, after a pointer check. II.4c swarm view. II.4d popups, menus,
  toast, drag.

## II.5 Blur

- Tested: layout `colors` and `background` accept `#rrggbbaa` and `terminal_opacity` works; `herdr-app shot` then
  has alpha (0.75 at the corner with 50 % grounds) and text stays solid. The X11 window has a 32-bit visual.
  On a private headless sway with a magenta desktop: as a native Wayland client (how the user runs it) the window is
  opaque, colours blended against black; started with `WAYLAND_DISPLAY` unset (XWayland) the desktop shows through.
  Not tested: Hyprland itself (a nested Hyprland 0.57 would not start on sway's `xdg_wm_base` v5), so the blur behind
  a see-through window is Hyprland's documented behaviour (the user's `decoration.blur` is on).
- A: run Herdr through XWayland with see-through grounds: the kitty look. Cost: at the user's scale 1.6 XWayland is
  blurry unless `xwayland.force_zero_scaling`, which then needs Herdr's zoom at 1.6 and changes every XWayland app.
- B: a Hyprland window rule `opacity` for class `herdr-app`: whole window fades, text included. Not tested.
- C: ask Herdr's author for a transparent Wayland window (`background_appearance` is in the binary, not exposed).
- Held by the user (round 2): no slices. They may move to an app of their own on hc, where this is one flag.

## II.6 Answer prompts in place

- Facts (read): hc's status record has `state` blocked, `kind` (permission, question, auth), `msg`, `title`; no
  options, and `swarm state` has none either. `hc read <t>` prints the screen, `hc keys <t> <key>` presses one, both
  with `machine/t`. An overlay window can hold a layout with `{terminal: address}`.
- Tier 1, always: a prompt row in Needs you (bar popup, Overview, All swarms) has Show terminal: the agent's live
  terminal in a window; the user types the answer.
- Tier 2: parse the prompt box at the foot of `hc read` (numbered options, one with the cursor; the command and
  reason above). Draw buttons only on a full match. On click read again and send `hc keys` only if the options'
  text is unchanged; else fall back to tier 1. "No, and say what" opens a field whose text is sent after the key.
- II.6a found (Claude Code 2.1.319, fixtures in `swarm/herdr/fixtures/prompts`): a `PermissionRequest` hook fires
  at every permission box and at AskUserQuestion, with `tool_name` and the full `tool_input` (Bash command, Write
  path and content, WebFetch url and prompt; AskUserQuestion's questions with header, options, descriptions and
  multiSelect). A `Notification` hook fires with `permission_prompt` for permission boxes only. hc's `msg` already
  names a question's options ("answer: Which color? (Red · Blue)"), only the first question's. The boxes: a title,
  the tool's detail between dashed rules, "Do you want to …?", options `❯ 1. Yes` with `❯` on the cursor, then
  "Esc to cancel · Tab to amend". The option set differs by tool (Bash 4, Write 3, Fetch 3 with "No, and tell
  Claude what to do differently (esc)"). Questions: `☐ Header` tabs, numbered options with description lines under
  them, "Type something", a rule, "Chat about this"; multiSelect has `[ ]` boxes and Next. The communicator
  answering by itself is out of scope.
- II.6d, the hook route (display only, decided with the designer): the swarm's settings template (not the user's
  settings) runs `swarm/herdr/prompt-hook.sh`: PermissionRequest records the hook's JSON to `<db dir>/prompts/<agent>.json`,
  PostToolUse and Stop clear it. Needs you (Overview, All swarms) shows its text in place of hc's msg, and only while
  hc's status for that terminal is blocked. The text is untrusted: plain, bounded, a long Write as its first lines and
  size; never run, and never what decides a key: buttons stay on II.6c's re-read rule. No blocking hook: a decision made
  by the hook could disagree with an answer typed in the terminal. Agents without the hook keep II.6c's screen text.
- Slices: II.6a spike: real permission and question prompts in the sandbox as parser fixtures; check the hook.
  II.6b tier 1. II.6c tier 2. II.6d the hook route.

## Part II build order (one builder, in sequence)

II.2a, II.1a, II.2b, II.2c, II.3a, II.3b, II.6a, II.6b, II.3d, II.1b, II.3c, II.3e, II.3f, II.3j, II.3g, II.3h,
II.3i, II.6c (and II.6d if the spike finds a hook), II.3k, II.3l, II.3m, II.4a, II.4b, II.4c, II.4d.

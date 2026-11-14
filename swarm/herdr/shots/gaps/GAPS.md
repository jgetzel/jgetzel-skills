# Rework build vs canvas: gap list (board #173, 2026-11-13)

Looked at: every canvas board rendered with headless Chrome (not kept; re-render from the canvas files), the live window
(shot 21:11; its crops `*-live.png` show the user's own window, so they are not in the repo: /tmp/claude-1000/-home-jgetzel-workspace-jgetzel-skills-ll-120/eda5a6db-2b11-408e-8c35-64aa5be025cb/scratchpad/gaps/), and the committed sandbox shots of slices 6 to 9
(`swarm/herdr/shots/swarm-tab.png`, `needs-you.png`, `large-swarm.png`). No new sandbox shots were made.
Crops are in this folder. Ordered by how much each closes the visual distance.

## 1. Palette (buildable: theme file + layout) -> task A
Canvas `swarmtab-canvas.png`, `rail-canvas.png`; built `rail-live.png`, `swarmtab-sandbox.png`.
The build shows Herdr's graphite: ground #101114, cards #17191d, light-blue focus ring. Canvas, sampled from the boards:

| theme name | canvas value | where |
| --- | --- | --- |
| canvas, chrome | #151110 | ground; the rail and bar sit on the same ground, no divider lines |
| background, surface, popover | #1e1917 | cards, terminals, pill group |
| hover | #262019 | active space, hovered row |
| selected | #352b26 | selected pill, selected row |
| border | #2c2421 | card and pill-group border |
| input | #382e2a | fields, swarm block border |
| foreground / muted / dim | #f0e7e0 / #b3a59b / #94867c | text |
| terminal foreground | #d9cfc7 | terminal text |
| accent, working | #e9a860 | amber |
| pane focus ring | #7a5a36 | dim amber, 1px (not the accent itself) |
| blocked | #ff806b | coral |
| done | #86b7ea | blue (also links, ansi blue) |
| green (ansi2) | #86c98f | landed, "green" |
| solid / solid_foreground | #f0e7e0 / #151110 | primary button |
| swarm block bg | #171312 | darker than ground |
| needs-you card | bg #2b1a17, border #6b3329 | |
| tree line | #5a4b44 | |

Layouts take a root `theme` and `colors` (AGENTS.md "The look"); `themes/<name>.json` holds terminal colours.
Nobody has picked a theme on rework (view.json has none), so the layout's own will show.

## 2. Swarm block missing in the live rail (bug) -> task B
Canvas `rail-canvas.png`; built `rail-live.png` (no block, communicator reads "claude", no Swarm pill in
`bar-live.png`) though the sandbox draws it (`rail-sandbox.png`).
Facts: `shared("rw-rail.swarms")` in the live window holds jgetzel-skills' summary with space
spd0e95763252278e75c9ff76af50e675c, and `hc ls --label herdr.space=<that>` lists the communicator (t1bf) and both
workers, so the data arrives and the space matches. high-perf-lean's summary (active, space spe73459...) runs fine by
hand but is absent from the shared list. One difference from rail-demo: live workers' terminals have
`parent` = the communicator's terminal, so they are kids of its tree, not trees of their own.
Cause (#175): the live spaces' `folder`s are rotated one space along (jgetzel-skills has /home/jgetzel, high-perf-lean
has the jgetzel-skills repo), so the rail keyed jgetzel-skills' summary to high-perf-lean's space and then dropped it
there (its `space` is another space). The rail, bar and All swarms now find a space's swarm by the summary's `space`
first, and each swarm agent heads its own tree. rail-demo.sh starts workers from the communicator's terminal.
Its real preset (#179) puts the folders off the same way: on the commit before the fix it draws no block
(`../real-preset-pre175.png`), on main it does (`../real-preset.png`).

## 3. Old Swarm side panel still in the layout -> task C (part needs the user)
Built `panel-live.png`; canvas has no side panel (`swarmtab-canvas.png`).
rework.json keeps jgetzel.json's `panel` column with files, changes, swarm, calendar. The user's panel is open on
swarm. Files / Changes / Calendar have no button in rw-bar. Canvas note: "Files, Changes, Calendar are cards like any
pane, not a separate right panel" (`cards-canvas.png`), but it draws no way to open them.

## 4. Swarm and agent screens -> task D
Canvas `swarmtab-canvas.png`, `asks-canvas.png`, `bar-canvas.png`; built `swarmtab-sandbox.png`, `asks-sandbox.png`,
`bar-sandbox.png`, `bar-live.png`.
- Cards inside a card: rw-swarm and rw-question draw bordered cards inside a pane that is itself a card with a
  "Swarm" / "Needs you" header. Canvas cards sit on the ground.
- Pills: built "claude ll-97"; canvas "ll-97", and the communicator's pill reads "Communicator". The pill group is
  lighter and thicker-bordered than the canvas's (#1e1917, 1px #2c2421).
- Communicator pane header: canvas "Communicator  ll-comms · your channel to the swarm" with Away at its right;
  built "claude ll-comms · done <1m", Away inside the Swarm pane.
- Bar subtitle: canvas "This computer · main green" for a swarm's space; built has no CI word.
- Hung toast at the rail's foot (Attention board): not built.
- Board card: Done / Dropped links; Landing: PR rows. Left out in slice 7.
- Built in #177 (`swarmtab-lookd.png`, `asks-lookd.png`, `board-done-lookd.png`): all six. The pane look is one for every
  pane, so the swarm tab's and Needs you's panes keep their frame's border; only their fill and header (empty ground)
  change. Landing's PR rows were already built (`gh pr list`); the sandbox has no GitHub repo, so its shots show none.

## 5. Rail weight (needs the user)
Canvas `rail-canvas.png`: space name 13px medium with "N tabs" under it, no chevrons, no guide line, machine heading
as small text. Built `rail-live.png`: 14px bold name, chevron, guide line, tab count at the right, machine line with
icon. The build is this way because of the user's own feedback (#168, e812eab8). Keep it, or go back to the canvas?

## Not buildable as drawn (known, UI-SPEC "Not buildable")
- The question inside the agent's card with the context column at the right (built: a pane above, cards in a row).
- Messages and Landing under the communicator's terminal (a mod pane can't be sized; splits are halves).
- The failed-shell mark.

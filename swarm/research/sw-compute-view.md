# sw-compute-view: compute claims in the Herdr swarm view's System section

Board #189. Shows what `swarm compute` knows (sw-compute.md §4) in rw-swarm's System section (UI-SPEC II.3i), with the
user's two controls: a machine's cap and its off switch. Not here: enforcement, priorities, the machine note, the
auto-spawner.

## Data path and refresh cost

The panel runs `swarm compute --json` itself, on its own timer; `swarm state` does not carry claims.

- Why not `state --view system`: that view is read every 3 s while System shows, and the ledger belongs to the machine,
  not to the swarm. `swarm compute` samples each machine for 0.5 s and makes one `hc exec` per connected remote machine,
  one after the other, so a read costs about 0.5 s plus one round trip per machine in wall time (1-2 s for this
  computer and two others) and almost no CPU (the sample is a `sleep`). A connected machine that hangs holds a read up
  to `hc exec`'s 20 s timeout.
- When: on opening System, then every 30 s while it shows (the Overview machine line's `QUIET_POLL`), never while a
  read is still running, and never more often than 3 times as long as the last read took. Right after a control
  succeeds, once more. Nothing reads it while System is not shown. One read every 30 s is under 7 % of one process's
  time, sleeping.
- Where: as every other call of the panel, `swarm compute` runs on the swarm's machine (`swarm(cwd, on, …)`), so for
  a swarm on another machine, "here" is that machine and its hc machines are the others.
- Between reads the card shows the last one and when it was read; a failed read keeps the last one and says why.

## Layout

The main thing shown: for each machine and each resource, how much is **claimed**, how much is **used without a
claim** (the user's own work, CI, a build started outside `swarm run`) and how much is **free**, so a waiting job's
reason can be read at a glance: the ledger is full, or unclaimed use takes the room.

One card, **Compute**, after "This computer" (memory) and before Locks. Its head: "Compute", note `read 12s ago`;
under it a legend of the four colours. Then a block per machine, this one first (named as the memory card names it),
the others by name:

```
This computer   off?                          9.3 busy of 24 cores           Cap…  Turn off
  Cores   [■■■■■■▒▒▒░░░░░░░░    ]   6 claimed · 3 unclaimed · 11 free · cap 20 of 24
  Memory  [■■■▒▒▒▒░░░░░░░░░░░░░]   10.0 claimed · ≈12.3 unclaimed · 57.7 free G
    sr-3      4 cores   8.0 G   4m   nix build .#x
    sr-5      2 cores   2.0 G   1m   cargo test
    waiting   sr-7   12 cores   2.0 G   2m   cores: claims fill the cap
vps             disconnected
```

- A stacked bar per resource over the machine's whole size: claimed (blue), unclaimed use (amber), free (green), and
  the rest, above the cap, as the bare track. The text beside it gives the same numbers, and `cap N of M` where the
  cap is below the machine's size.
- **Cores**, as admission counts them (sw-compute.md §1): claimed `cc` is the ledger's sum; unclaimed is the script's
  `outside` = `max(0, round(busy - cc) - max(1, ncpu/8))`, busy cores no claim explains past the noise allowance; free
  is the script's `min(lim - cc, ncpu - cc - outside)`, floor 0, with `lim` the cap less the user's reservation
  (`limit_cores` of `swarm compute --json`, the cap where an older swarm gives none). So claimed + unclaimed + free + above the cap is the
  machine's cores, and free is what the next `try` is granted. The measured busy cores are on the machine's line.
- **Memory**: the ledger knows what was claimed, not what claimed jobs use, so unclaimed use is an estimate, `max(0,
  total - available - claimed)`, written `≈` and named an estimate in the legend. Free is admission's `min(cap -
  claimed, available)`, floor 0. Claimed + unclaimed + free never exceeds the total (free is at most cap - claimed, and
  with unclaimed above 0 claimed + unclaimed is what is in use).
- `off` is an amber chip on the machine's line; a machine `hc machine ls` does not show connected, or one that did not
  answer, is one dim line saying so (`disconnected`, `unreachable`, …) with no bars and no controls.
- Under it, its claims, oldest first: who (opens that agent's page when it is in this swarm), cores, memory, age, the
  command in the monospace font, truncated. Then its waiters, oldest first: a `waiting` chip, who, cores, memory, how
  long, and why: for each resource it is short of, `claims fill the cap` (it asks for more than cap - claimed) or
  `unclaimed use takes the room` (it would fit under the cap); if it is short of neither, `behind <older waiter>`, or
  `fits: starts on its next try` for the oldest. A waiter the reservation holds out says `held by the reservation`, one that unclaimed use holds out
  (it would not fit even with every claim ended) `held by unclaimed use`; a
  `--cores all` one says `held: reserved, unclaimed use, cap below the machine` (the reasons that apply) or, when only
  claims stand in its way, `waits for an empty machine`. The panel has no reserve control yet.
- An `off` machine still lists its claims: running jobs finish.
- With no claim and no waiter anywhere, one dim line under the machines: "No job claims cores now: `swarm run`
  claims them".
- Narrow (the side view, one column): a machine's line wraps, the bars' text goes under the bars.

## What a click does

- **Cap…** opens a form under that machine's row (one at a time): `Cores [20] of 24` and `Memory [80] G of 94`, each
  prefilled with the current cap, `all` when the cap is what the machine has. A whole number of cores, a decimal number
  of G, or `all` (empty is `all` too). Save (or Enter) runs `swarm compute cap <machine|here>` with `--cores` and
  `--mem` for the fields that changed; nothing changed closes it. A bad value says so under the form and runs nothing.
- **Turn off** runs `swarm compute off <machine|here>`; **Turn on**, `swarm compute on …`. One click each: both are
  undone by the other button, and running jobs are untouched.
- A control's failure shows in the card's head as the other cards' flash does. After success the card reads again.

## Checking it

The screenshot sandbox (shot.sh `--rework real`, board #179) gives "desktop" a ledger and a reading of its own:
rail-demo.sh starts it with `SWARM_COMPUTE_DIR` (a test hook of the script: the ledger's directory) and a made-up
`/proc/stat` and `/proc/meminfo` through `SWARM_COMPUTE_STAT` and `SWARM_COMPUTE_MEM`: 16 cores of which 15 are busy
(a counter that advances while the sandbox lives), 64 G with 40 G available. This computer keeps its real reading.
`compute-demo.sh none | claims | off` empties the two ledgers, or writes two claims here and three on desktop under a
cap of 14 cores with two waiters (one held back by unclaimed use, one by the cap; holder `t`, an hour), and for `off`
turns desktop off. Shots in swarm/herdr/shots/compute-*.png; the controls were clicked with xdotool in the sandbox and
`swarm compute` printed before and after each.

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

One card, **Compute**, after "This computer" (memory) and before Locks. Its head: "Compute", note `claims through
swarm run · read 12s ago`. Then a row per machine, this one first (named as the memory card names it), the others in
`hc machine ls` order:

```
This computer   [■■■□□] 6 of 20 cores   [■□□□□] 10.0 of 80 G   9.3 busy   cap 20 of 24     Cap…  Turn off
    sr-3        4 cores   8.0 G   4m   nix build .#x
    sr-5        2 cores   2.0 G   1m   cargo test
    waiting  sr-7   12 cores   2.0 G   2m
desktop         [□□□□□] 0 of 16 cores  [□□□□□] 0.0 of 64 G    0.0 busy   off              Cap…  Turn on
vps             disconnected
```

- The machine row: cores claimed against the cap (a 5 px meter as the memory card's and the text), memory claimed
  against the memory cap, measured busy cores, and `cap N of M` when a cap is below what the machine has (cores or
  memory). `off` is an amber chip; a machine `hc machine ls` does not show connected, or one that did not answer, is
  one dim row saying so (`disconnected`, `unreachable`, …) with no meters and no controls.
- Under it, its claims: who (opens that agent's page when it is in this swarm), cores, memory, age, the command in
  the monospace font, truncated. Then its waiters, oldest first: a `waiting` chip, who, cores, memory, how long.
- An `off` machine still lists its claims: running jobs finish.
- With no claim and no waiter anywhere, one dim line under the rows: "No job claims cores now: `swarm run` claims them".
- Narrow (the side view, one column): the row wraps, the buttons go to a second line.

## What a click does

- **Cap…** opens a form under that machine's row (one at a time): `Cores [20] of 24` and `Memory [80] G of 94`, each
  prefilled with the current cap, `all` when the cap is what the machine has. A whole number of cores, a decimal number
  of G, or `all` (empty is `all` too). Save (or Enter) runs `swarm compute cap <machine|here>` with `--cores` and
  `--mem` for the fields that changed; nothing changed closes it. A bad value says so under the form and runs nothing.
- **Turn off** runs `swarm compute off <machine|here>`; **Turn on**, `swarm compute on …`. One click each: both are
  undone by the other button, and running jobs are untouched.
- A control's failure shows in the card's head as the other cards' flash does. After success the card reads again.

## Checking it

The screenshot sandbox (shot.sh `--rework real`, board #179) gets a ledger of its own for "desktop": rail-demo.sh
starts it with `SWARM_COMPUTE_DIR` (a test hook of the script: the ledger's directory) and a made-up `/proc/stat`
and `/proc/meminfo` (16 cores, 64 G) through `SWARM_COMPUTE_STAT` and `SWARM_COMPUTE_MEM`. `compute-demo.sh none |
claims | off` writes claims and a waiter into the two ledgers (holder `t`, an hour), or turns desktop off. Shots: no
claims, claims and a waiter, a machine off; then the controls clicked in the sandbox and `swarm compute` printed
before and after.

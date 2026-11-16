# sw-compute-backfill: the `claim` tool, backfill, exclusive jobs, the user's reservation, and proofs of admission

Designed 2026-11-15 on top of [sw-compute.md](sw-compute.md) as built (its §6a); the user's decisions on the first
draft are in §11. What it adds:

- compute claims move out of the swarm CLI into a standalone tool, `claim`, a Lake package of its own that swarm uses
  (§1a);
- backfill past a waiting head (§2), with estimates from a cmd-cost history that keeps every `swarm run` job (§2.1);
- `--cores all` as an exclusive claim on the whole machine (§2.4);
- jobs at the lowest CPU and I/O priority (§4);
- the user's reservation, `claim reserve` (§3).

§6 is a pure Lean model of admission with the theorems the build must satisfy, and §7 ties the shipped `sh`/`awk`
script to that model. Nothing here adds a daemon (§10 says what a later one keeps): admission is still one script run
on the target under its `mkdir` lock.

## 1. What changes, in one paragraph

Today `try` grants iff the request fits and no older live ticket exists, so a big waiter holds back every small job
until the ledger empties. Now the oldest waiting ticket that can run (the **head**) gets an estimated start, its
**shadow**: the earliest expected end of running claims at which it would fit. A younger request that fits now is
granted if its own expected end (now + the 90th percentile of its recent wall times) is no later than the shadow (EASY
backfill, as Slurm's `sched/backfill` with one reservation). Expected durations travel in the claim lines and the `try`
arguments. `--cores all` asks for the whole machine alone; while the user's reservation or unclaimed use keeps it off,
it waits without blocking anyone. A per-machine `reserve` file holds the user's reservation, separate from the cap;
the room sized jobs may take is `min(cap, size - reserve)`. Jobs run under `nice -n 19` and, where it works,
`ionice -c3`.

## 1a. The tool: `claim`

`claim` owns the ledger, admission (with backfill and exclusive claims), the cap and the reservation; `swarm run` and
`swarm compute` are its clients. Anything can claim and wait with it without swarm and outside a git repo: CI on the
desktop, the user's shell, a Noctalia plugin.

### Interface

The script's ops are the public interface, in the shape §5's table gives them:

```
claim op <machine|here> <try|drop|ls|cap|reserve|off|on> <args…>    # the op's output as is; exit 1: no answer, 2: bad args
claim [--json] [here|<machine>]                                    # what `swarm compute` shows (§3.1, §3.2)
claim cap|reserve|off|on <machine|here> …                          # as `swarm compute`'s, in the user's terms
claim run [--cores N|all] [--mem G] [--est S] [--who NAME] -- <cmd…>   # here: claim, wait, run at low priority (§4), drop
```

- `claim run` sizes from its flags only (default 2 cores and 2 GiB, no estimate, so no backfill); the history keyed by
  repo stays in `swarm run`. Its holder is `p<its pid>`, `who` defaults to `$USER`, its exit code is the command's,
  255 when nothing can ever fit (as `swarm run`). CI: `claim run --cores 8 --mem 16 --est 900 -- make check`; a
  benchmark: `claim run --cores all -- ./bench`.
- A caller that holds a claim across its own steps loops `claim op here try <id> … p$$ …` until `ok`, and ends with
  `claim op here drop <id>`.
- `swarm compute …` is `claim …` (the same library function, flags and output, kept so briefs and panels need no
  change). `swarm run` keeps what is about swarm: the sizing and estimate from cmd-cost, the sync, the remote job, the
  recording. It calls the library, not a subprocess, for the claim and the wait loop (`Claims.acquire`, moved out of
  Run.lean). The one seam is `Claims.call (host) (mach : Option String) (args : List String) : m (Option String)`
  (today's `Compute.sh`): every op goes through it.
- Targets need nothing installed. The script still travels as a string: `sh -c SCRIPT sh <op> …` here, through
  `hc exec --on <m>` elsewhere. `claim` needs `hc` only for other machines (`hc machine ls`, `hc exec`).
- The ledger directory `swarm-compute` and the `SWARM_COMPUTE_*` variables keep their names.

### The package

A Lake package of its own at the top of the repo, `claim/`; the Lean library and namespace are `Claims` (a `Claim`
namespace would clash with the `Claim` structure inside it); the executable is `claim`.

```
claim/
  lakefile.lean      package claim: lean_lib Claims, lean_exe claim (root Main), lean_lib ClaimTests, lean_exe claim-tests
  lean-toolchain     the same line as swarm/lean/lean-toolchain
  Main.lean
  Claims/            Admit (§6.1), Ledger (script, parse, render, json), Machines, Acquire, Cli, Host, Util,
                     Proofs (§6.2), Assumptions (§7)
  Tests/             Ledger (#guards), Script, Spec (§7, the claims_spec group), Cli
  Audit.lean  build.sh  check.sh  claim (the launcher)
```

- **It depends on nothing of swarm**: only Lean core (`Lean.Data.Json` for `--json`). It carries its own few string
  helpers (`words`, `parseInt`, `parseFloat`, `fixed`, `splitlines`, `shquote` in `Claims/Util.lean`; shortcut: a
  dozen lines duplicated from swarm's `Util`, to merge if swarm ever imports them from here). It reaches the world
  through a record, `Claims.Host m` (`run : List String → m (Option (Int × String))` for exit code and stdout,
  `sleep`, `err`, `now`), which `Main.lean` fills with `IO` and swarm fills from its `Sys`/`Proc`/`Clock`/`Env`
  classes. No sqlite, no C shim.
- **swarm requires it by path**: `require claim from ".." / ".." / "claim"` in `swarm/lean/lakefile.lean` (and in
  `swarm/lean/hpl/lakefile.lean`, where claim's modules build stock); `swarm/lean/lake-manifest.json` gains the path
  entry. A path dependency builds in its own `claim/.lake`.
- **Toolchains**: the two `lean-toolchain` files are the same line; `claim/check.sh` and `swarm/lean/check.sh` `cmp`
  them, and the flake checks both against nixpkgs' `lean4`.

| Today | Moves to |
|---|---|
| `SwarmLean/Lib/Compute.lean`: the script, `BUSY_AWK`, `DARWIN_MEM_AWK`, `Try`, `parseTry`, `sh`, `release`, `Claim`, `Ticket`, `Ls`, `parseLs`, `gi`, `span`, `render`, `json` | `claim/Claims/Ledger.lean`; `sh` becomes `call` |
| `hcMachines` (`SwarmLean/Lib/Run.lean`) | `claim/Claims/Machines.lean`; swarm uses it from there |
| Run.lean's claim loop (candidates, `try`, the waiting lines, exit 255) | `claim/Claims/Acquire.lean`, `acquire` |
| `Cmd/Compute.lean`'s body | `claim/Claims/Cli.lean`; `swarm compute` calls it |
| `lowPrio` (§4) | `claim/Claims/Ledger.lean`; `claim run` and `swarm run` use it |
| `size`, `history`, `estimate`, `DEFAULT_*` (cmd-cost, by repo) | stay in `SwarmLean/Lib/Compute.lean` |
| the script's cases in `Tests/Cli/Compute.lean`, the ledger `#guard`s in `Tests/Compute.lean` | `claim/Tests/Script.lean`, `claim/Tests/Ledger.lean` |
| (new) §6.1's model, §6.2's proofs, §7's assumption and cases | `claim/Claims/Admit.lean`, `Proofs.lean`, `Assumptions.lean`, `claim/Tests/Spec.lean` |

The `swarm run` and `swarm compute` tests stay in swarm's `Tests/Cli/Compute.lean`, with the fixture's
`SWARM_COMPUTE_STAT`/`_MEM`/`_POLL_MS` as today. `claim/Tests/` has its own small harness (a scratch dir, `sh`,
compare); it does not use swarm's fixture.

### Built, installed, gated

- **Build**: `claim/build.sh` runs `lake build claim claim-tests` there (elan), else `nix build ..#claim -o .lake/nix`;
  `swarm/lean/build.sh` runs it first (lake then builds swarm-lean against the same `claim/.lake`).
- **Launcher**: `claim/claim`, as `swarm/swarm` is for swarm-lean: runs `claim/.lake/build/bin/claim`, else
  `claim/.lake/nix/bin/claim`, with the same one-line notice when the binary is older than `claim/`'s sources, and
  says how to build when there is none. `swarm/swarm`'s staleness `find` adds `../claim/Claims`,
  `../claim/lakefile.lean` and `../claim/lean-toolchain`, since swarm-lean is built from them.
- **install.sh** builds (through swarm's `build.sh`) and links `~/.local/bin/claim` to `claim/claim`, making the
  directory and skipping a real file there, so CI and a desktop plugin find it without a session's PATH.
- **Flake**: a new `claim` derivation (`cd claim && lake build claim`, installs `.lake/build/bin/claim`, no sqlite),
  `packages.claim`, and `claim` in the `default` env (`nix profile install .#claim` for a machine without a checkout).
  `swarm-lean`'s derivation is unchanged but for checking both toolchain files: its `lake build` builds claim's library
  from `src = self`.
- **The gate**: `claim/check.sh` refuses `sorry`, `admit`, `native_decide` and `axiom` under `claim/`, builds, runs
  `claim/Audit.lean` (every `Claims` theorem on Lean's three axioms; each assumption of `Claims/Assumptions.lean`
  with the theorems taking it; its `(claims_spec: …)` tag must name a `claim-tests --list` case), and runs
  `claim-tests`. `swarm/lean/check.sh` runs `../../claim/check.sh` first and fails with it. swarm's `Audit.lean` is
  unchanged: its `ours` does not cover `Claims`, which claim's own audit does.
- **A new worktree** needs a same-commit peer's `claim/.lake` copied as well as its `swarm/lean/.lake`, the same way
  (it is not under `swarm/lean/.lake/packages`).

Below, `swarm compute X` (§3) is also `claim X`.

## 2. Backfill

### 2.1 The history and the estimates

The cmd-cost history (cmd-cost.md) changes in three ways:

- **`swarm run` records every job it runs**, here and on another machine, as a `source='run'` row with no threshold:
  `Cost.recordSql`'s gate becomes `source == "run" || wall_s >= MIN_WALL || peak_kb >= MIN_PEAK_KB`. A local job's
  row is new (today only remote jobs write one): `wall_s` is the job's time from its claim to its end (the footer's),
  `cpu_s` and `peak_kb` 0 (watchd measures the agent's command, as today). Every `run` row is keyed by the user's
  command, `key := Cost.key line`, as the lookup is (§6a.6); today a remote row is keyed by the prefixed command and
  is never found when `run.prefix` is set.
  Other sources keep the thresholds: watchd's `swarm` rows are every Bash command of every agent (`ls`, `git status`,
  `grep`), and without the floor the table would be mostly those, drowning `swarm cost --top` and the machine note;
  they are not what the estimate reads. `repo` rows are written by a repo's script with `sqlite3`, not through
  `recordSql`, so no threshold ever applied to them.
- **No pruning**: `Cost.KEEP` and `recordSql`'s `delete` go; every row stays, for later analysis. A row is about
  150 bytes; a busy machine's few hundred to a thousand rows a day is under 60 MB a year, so no retention limit. A new
  index `cmd_rk on cmd(repo, key, id)` serves the window below, which reads across machines.
- **A window**: `history` reads the newest 50 rows of this repo and key, any machine
  (`… where repo=? and key=? order by id desc limit 50`). 50, because the estimate is a 90th percentile: of 50 rows it
  is the 45th, so up to five outliers (a cold cache, a hung run) do not set it, where of 20 two would; and 50 runs of
  one command is days to a couple of weeks of swarm work, recent enough to follow a codebase that grows. `size` reads
  the same window (all its rows, as today's rule). The machine note's `Cost.predict` reads the newest 50 for this
  machine (it read all, at most 20, before). `swarm cost --top` reads every row.
- So `swarm cost` and the machine note's medians now include short jobs (the `run` rows of jobs under a minute).

The estimates:

- **A request's estimate** `est_s` (`Compute.estimate (rows) : Option Int`, beside `size`): over the window's `run`
  rows with `wall_s > 0`, the nearest-rank 90th percentile of `wall_s` (sorted ascending, the `⌈0.9 n⌉`-th, 1-based;
  for `n < 10` that is the largest, so "fewer than 5 rows: the largest" holds by itself); none without such a row.
  Only `run` rows: they time a job from its claim to its end, which is what a claim holds; a `swarm` row times the
  agent's `swarm run …` command, its waiting included. `--cores`/`--mem` do not change it.
- **A running claim's estimate** is the one its request carried, written into its claim line (§2.3). Its expected
  end is `start + est_s`; a claim past its expected end (overdue) is expected to end **now**.
- Wall time depends on the cores a job got; the history does not record them. Shortcut, stated in the docs.

### 2.2 The rule

Inside `try`, after `clean`, with `fc`, `fm` as today but over the reserve-aware limit (§3):

```
held(t)    = sized t:     t.cores > lim_cores or t.mem > lim_mem           # the reservation keeps it out
             exclusive t: reserve != 0 0, or outside > 0, or a cap below the machine     (§2.4)
ahead      = live tickets t != me, not held, (t.first, t.id) < (my first, my id)     # ids compared bytewise (LC_ALL=C)
head       = the least of `ahead` by (first, id)
end(c)     = max(now, c.start + c.est)        for a claim with an estimate; a claim without one has no expected end
events     = {now} ∪ {end(c)}
free_at(τ) = (fc + Σ cores, fm + Σ mem) over claims with end(c) <= τ
fits_at(h, τ) = sized h:     h.cores <= free_at(τ).cores and h.mem <= free_at(τ).mem
                exclusive h: every claim has end(c) <= τ
shadow     = the least τ in events with fits_at(head, τ); none if no τ

grant iff  fits now and ( ahead is empty or (my est is known and shadow is known and now + est <= shadow) )
           where fits now = sized: cores <= fc and mem <= fm;  exclusive: no live claim, reserve 0 0, outside = 0
```

- **No history, no backfill.** A request without an estimate is granted only when nothing is ahead of it (today's
  rule). Since every `swarm run` job is now recorded (§2.1), only a command's first run lacks one; guessing it would let
  a new 30-minute build delay the head by 30 minutes.
- **A running claim without an estimate never ends, in the model**, rather than "makes the head's start unknown". The
  head's shadow is then none only if it needs that claim's room, and a claim it does not need does not stop backfill.
  This is sound for the theorem (§6, `backfill_no_delay`): the shadow counts only room that estimates promise.
- **Shadow none forbids backfill.** That covers unknown claims the head needs and unclaimed use (`outside`, low
  `MemAvailable`) the ledger cannot promise to free. An exclusive head is held in the cases its shadow would be none for
  a reason other than claims (§2.4), so it never stops backfill that way.
- Only the head is protected. A younger request may pass an older non-head waiter; that waiter is protected once it
  is the head. Held tickets are neither ahead nor head, and a held sized request cannot fit (`cores > lim >= fc`).
- Model assumptions, stated in the docs: measured unclaimed use stays as it is; memory a claim frees becomes
  available; estimates are what jobs take. None of these is checked; the theorems are about the estimates.

### 2.3 Where the numbers travel

- `try` gains `<est_s|->` after `<mem_kb>`: `try <id> <cores|all> <mem_kb> <est_s|-> <holder> <who> <cmd>`. The
  script ships with the binary that calls it (`sh -c SCRIPT`), so op arguments and output lines need no compatibility.
  `ok` now says what was granted: `ok <cores> <mem_kb>` (an exclusive claim's memory is decided by the script).
- **Claim line**: `cores mem_kb holder start [~est_s] who cmd…`. `~<n>` is written only when the estimate is known,
  so a claim without one is byte-for-byte today's line. `who` is sanitised to `[A-Za-z0-9._:-]`, so a fifth field
  starting with `~` is always the estimate. The remote job script's holder rewrite (`sed` on field 3) is unchanged.
- **Ticket line**: `first cores mem_kb who`, with `cores` the word `all` and `mem_kb` 0 for an exclusive request.
  `try` now **rewrites** its ticket on every `wait` (keeping `first`) instead of touching it. Tickets need no estimate:
  only the head's size enters the rule.
- **Old lines** (a ledger written before this change): a claim without `~` has no estimate; a ticket reads as a sized
  one; no `reserve` file is a reservation of 0. Older binaries ignore the `reserve` file and fail to parse an `all`
  ticket; the user upgrades every machine when this lands (§11).

### 2.4 `--cores all`: the whole machine, alone

For benchmarks (hpl-comms' cross-language runs): no other job, and the user off the machine.

- **Granted** when the usual ahead/backfill rule allows and: no live claim, the reservation is `0 0`, and `outside`
  is 0 (busy cores past the claims, here none, within the noise floor `max(1, ncpu/8)`). It claims `ncpu` cores and
  the available memory (`avail_kb`) at that moment; the job gets those as `SWARM_CORES` and `SWARM_MEM_KB`.
- **The cap**: an exclusive request needs a cap at or above the whole machine (cores `>= ncpu` and memory
  `>= total_kb`, as `-` is); under a lower cap it is `never`. The cap is what jobs may ever take, and a standing cap
  below the machine says part of it is not for jobs; the user lifts it (`claim cap here --cores all --mem all`) to
  run a benchmark. `swarm run`'s 255 message says so.
- `--mem` with `--cores all` is refused by both CLIs (the memory is all that is available).
- **Held, so it blocks no one**: while the reservation is not `0 0`, `outside > 0`, or the cap is below the machine
  (lowered after it queued), an exclusive ticket is held: neither ahead of anyone nor head. Otherwise only claims
  stand in its way, and it is an ordinary head whose shadow is the first event by which every claim has ended by its
  estimate (none if a claim has no estimate: then nothing backfills past it, as for any head that needs an unknown
  claim). It may flip between held and not as the user works; it runs when the machine is quiet and empty.
- **Alone while it runs**: a request must ask for at least 1 core (the script refuses 0, `bad size`), so with an
  `ncpu`-core claim live nothing else fits (`fc <= ncpu - cc - outside <= 0`). The claim line is an ordinary one.

## 3. The user's reservation

- A file `reserve`, `cores mem_kb`, both whole numbers; absent is `0 0`, and writing `0 0` removes it. Separate from
  `cap`, composed by `min`:

  ```
  res_c = min(ncpu, reserve_cores)          res_m = min(total_kb, reserve_mem_kb)      # clamped when read
  lim_c = min(cap_cores, ncpu - res_c)      lim_m = min(cap_mem_kb, total_kb - res_m)
  fc    = min(lim_c - claimed_cores, ncpu - claimed_cores - outside)        # was cap_cores - claimed_cores
  fm    = min(lim_m - claimed_mem, available_mem)
  ```
- Why a separate file and not sugar over `cap`: a standing cap (say 20 of 24 on a shared box) and a reservation both
  hold, and `reserve <m> 0` returns to the standing cap; as sugar, `reserve 0` would have to set the cap to all and
  erase it, or save the old cap in a second file anyway. And the two mean different things to a waiting job: above
  the **cap** it can never run (`never`, and `swarm run` exits 255 when nothing waits), above the **reservation** it
  waits for the user (held, §2.2), without blocking smaller jobs behind it.
- Reservation and measurement do not add up: `fc` is the smaller of the ledger's room and the measured room, so the
  user's own use up to the reserved cores costs jobs nothing more.
- `all` is exclusive (§2.4): any reservation holds it.
- `never` stays against the cap only. Nothing running is stopped when a reservation is made; new claims wait.
- CLI: `claim reserve <machine|here> <cores> [--mem G]` (and `swarm compute reserve …`). `<cores>` a whole number
  >= 0, `--mem` decimal GiB >= 0 (as `cap`'s), **omitted is 0**: the command states the whole reservation, so
  `reserve here 0` lifts it all, and a slider passes both values. Larger than the machine is accepted and shown
  clamped. Prints nothing; exit 0, or `die` as `cap` does (unknown machine, bad number, no answer).
- `claim [--json] [here|<machine>]`: one machine only (one `hc exec` instead of one per machine), for a desktop widget
  that polls.

### 3.1 What `claim` (and `swarm compute`) shows

```
here: 8 of 16 cores claimed (cap 20 of 24, 4 reserved, 9.3 busy), 10.0 of 72.0G claimed (8.0G reserved, 61.2G available)
  sr-3   6 cores  8.0G  4m of ~10m  nix build .#x
  sr-5   2 cores  2.0G  1m  cargo test
  waiting: sr-7 18 cores 2.0G 2m, held by the reservation
  waiting: bench whole machine 5m, held: reserved, unclaimed use
```

`N of L` is claimed of `lim` (today: of the cap; the same when nothing is reserved and the cap is at most the
machine). `, N reserved` / `N.NG reserved, ` only when non-zero. `of ~10m` when the claim has an estimate. A held
exclusive waiter names each reason: `reserved`, `unclaimed use`, `cap below the machine`.

### 3.2 `--json`, the fields a desktop plugin reads

Per machine, as today plus the new fields (marked +):

```json
{"here": {"ncpu": 24, "busy": 9.3, "total_kb": 83886080, "avail_kb": 64161000,
          "cap_cores": 20, "cap_mem_kb": 83886080, "off": false,
          "reserve_cores": 4, "reserve_mem_kb": 8388608,                          (+, in effect: clamped)
          "limit_cores": 20, "limit_mem_kb": 75497472,                            (+, lim_c / lim_m)
          "claims": [{"cores": 6, "mem_kb": 8388608, "holder": "p31", "start": 1763200000,
                      "est_s": 600, "who": "sr-3", "cmd": "nix build .#x"}],      (+ est_s: int or null)
          "queue": [{"first": 1763200100, "cores": 18, "mem_kb": 2097152, "who": "sr-7",
                     "exclusive": false, "held": true}]},                         (+ exclusive, held)
 "laptop": {"state": "disconnected"}}
```

An exclusive waiter has `"exclusive": true`, `cores` the machine's `ncpu` and `mem_kb` 0. A Noctalia toggle/slider
needs `ncpu` and `total_kb` (the ranges), `reserve_cores` and `reserve_mem_kb` (the positions), `limit_cores` and the
claims' cores (what jobs may use, what they use), and calls `claim reserve here <n> --mem <G>`; reading
`claim --json here` costs the 0.5 s busy sample and no `hc exec`. `limit_*` and `held` are computed by the model's own
functions (§6.1), so a panel does not copy the formula.

## 4. Lowest priority for jobs

- `swarm run` and `claim run` start the job command (here and, for `swarm run`, on another machine) as
  `if ionice -c3 true 2>/dev/null; then exec ionice -c3 nice -n 19 sh -c "$1"; else exec nice -n 19 sh -c "$1"; fi`
  (`Claims.lowPrio (cmd) : String` builds it; here `sh -c (lowPrio full)`, there it replaces `{full}` inside the job
  script's subshell, after the exports). The exit code is the job's.
- Linux: `ionice -c3` is the idle I/O class, allowed for one's own processes without privilege; it takes effect
  under the BFQ I/O scheduler and is ignored by `none`/`mq-deadline`. Probing with `ionice -c3 true` covers a system
  without `ionice` or one that refuses it.
- macOS: no `ionice`, so `nice -n 19` only. `taskpolicy -b` would lower I/O priority too, but it also confines the
  job to the efficiency cores on Apple silicon, which is a slowdown, not a priority.
- Not reached, said in the docs and not solved: a `nix build`'s builds run in the nix daemon, not under the job, so
  they keep the daemon's priority. On NixOS the daemon's own priority is a system setting
  (`nix.daemonCPUSchedPolicy = "idle"`, `nix.daemonIOSchedClass = "idle"`). The sync, `git add` and the job script's
  bookkeeping on the other machine run at normal priority.
- An exclusive benchmark runs niced too; on a machine it has to itself that costs nothing.

## 5. The script

Still one POSIX `sh` string, now in `claim/Claims/Ledger.lean`. Changes:

- The decision moves into one awk program, `ADMIT_AWK`, a Lean string constant like `BUSY_AWK`, so it can be run and
  tested alone (§7). Called as `LC_ALL=C awk -v … "$ADMIT_AWK"` (also fixes the `sort` tie-break, which compared ids
  in whatever locale the caller had: two callers with different collation could each see the other ahead).
- `caps()` also reads `reserve` and sets `resc resm limc limm` (§3).
- `try` refuses `cores` 0 (`bad size`, exit 2); `all` is passed to the awk as the word, with `mem` 0.
- Test hooks, as §6a's: `SWARM_COMPUTE_NOW` (the script's `now`) and `SWARM_COMPUTE_BUSY` (busy cores; skips the two
  `/proc/stat` reads and the 0.5 s sleep, Linux branch).

`ADMIT_AWK`'s contract (the differential test depends on it exactly):

- Variables: `now ncpu total busy avail capc capm resc resm limc limm off id first cores mem est`; `busy` decimal,
  `cores` a number or `all`, `est` a number or `-`, `resc resm` the file's values (unclamped, 0 without the file),
  `first` the requester's ticket's first epoch or `now`, everything else whole numbers.
- Input lines: `c <claim line>` per live claim, `q <id> <ticket line>` per live ticket (the requester's own included;
  the program skips `id`).
- Output: exactly one line, `off` | `never <capc> <capm>` | `ok <cores> <mem_kb>` |
  `wait <max(0,fc)> <max(0,fm)> <ahead>`, decided as `Admit.decide` (§6.1). `outside` as today:
  `k = max(1, int(ncpu/8)); max(0, int(busy - cc + 0.5) - k)`.

`try` after the awk: `ok c g` writes the claim `c g holder now [~est] who cmd` and removes the ticket; `wait` writes
`first cores mem who` to the ticket; `never` and `off` remove the ticket. It prints the awk's line.

| Op | Does | Prints |
|---|---|---|
| `try <id> <cores\|all> <mem_kb> <est_s\|-> <holder> <who> <cmd>` | admission (§2.2-§3) by `ADMIT_AWK`; writes the claim and removes the ticket, or rewrites the ticket | `ok <cores> <mem_kb>`, `wait <free_cores> <free_mem_kb> <ahead>`, `never <cap_cores> <cap_mem_kb>`, or `off` |
| `drop <id>` | removes the claim and the ticket | |
| `ls` | | `ncpu busy total_kb avail_kb cap_cores cap_mem_kb off reserve_cores reserve_mem_kb` (reserve clamped), then `c <claim line>` and `q <ticket line>` rows |
| `cap <cores\|-\|=> <mem_kb\|-\|=>` | writes `cap` | |
| `reserve <cores> <mem_kb>` | writes `reserve`; `0 0` removes it; not a number: `bad reserve`, exit 2 | |
| `off`, `on` | makes or removes `off` | |

`parseTry` reads `ok c g` (`Try.ok cores mem`). `parseLs` takes exactly the 9-field header (a binary only parses its
own script's output), a claim row with or without the `~` field, and a ticket row with `all`; `Claim` gains
`est : Option Int`, `Ticket.cores` becomes `Option Int`, `Ls` gains `res_cores res_mem_kb`.

## 6. The model and the theorems

### 6.1 The model: `claim/Claims/Admit.lean`

Pure, no imports beyond core. The build writes these as plain definitions (Sonnet); the names and shapes below are
the contract the proofs and the differential test use.

```lean
namespace Claims.Admit

/-- A live claim: its size, its start, its estimate (none: unknown, and every old line). -/
structure Claim where
  cores : Int
  mem : Int
  start : Int
  est : Option Int

/-- A live ticket; `cores` none: exclusive (`all`). -/
structure Ticket where
  id : String
  first : Int
  cores : Option Int
  mem : Int

/-- The machine and its ledger as `try` reads them under the lock, after `clean`. -/
structure Machine where
  ncpu : Int
  total : Int
  busy : Int                         -- hundredths of a core (the script's %.2f)
  avail : Int                        -- KiB
  cap : Option Int × Option Int      -- the cap file; none: `-`, or no file
  res : Int × Int                    -- the reserve file; (0, 0): none
  off : Bool
  now : Int
  claims : List Claim
  tickets : List Ticket              -- every live ticket, the requester's own included

/-- A request; `cores` none: exclusive (`all`), and then `mem` is ignored. -/
structure Req where
  id : String
  cores : Option Int
  mem : Int
  est : Option Int

inductive Answer
  | ok (cores mem : Int) | wait (fc fm ahead : Int) | never (capc capm : Int) | off
  deriving BEq, Repr

/-- The room sized jobs may take of `size`: the cap, less the reservation clamped to the machine. -/
def lim (cap size res : Int) : Int := min cap (size - min size (max 0 res))

def capC (m : Machine) : Int := m.cap.1.getD m.ncpu
def capM (m : Machine) : Int := m.cap.2.getD m.total
def limC (m : Machine) : Int := lim (capC m) m.ncpu m.res.1
def limM (m : Machine) : Int := lim (capM m) m.total m.res.2
def cc (m : Machine) : Int := (m.claims.map (·.cores)).sum
def cm (m : Machine) : Int := (m.claims.map (·.mem)).sum
def outside (m : Machine) : Int := max 0 ((m.busy - 100 * cc m + 50).tdiv 100 - max 1 (m.ncpu / 8))
def freeC (m : Machine) : Int := min (limC m - cc m) (m.ncpu - cc m - outside m)
def freeM (m : Machine) : Int := min (limM m - cm m) m.avail

/-- No cap below the whole machine. -/
def whole (m : Machine) : Bool := capC m ≥ m.ncpu && capM m ≥ m.total
/-- Nothing but claims keeps an exclusive job off: no reservation, no unclaimed use past the noise floor. -/
def quiet (m : Machine) : Bool := m.res == (0, 0) && outside m == 0

def held (m : Machine) (t : Ticket) : Bool := match t.cores with
  | some c => c > limC m || t.mem > limM m
  | none => !whole m || !quiet m

/-- (first, id) order; String's `<` is bytewise on these ids, as LC_ALL=C. The one place the queue order is set. -/
def before (a b : Int × String) : Bool := a.1 < b.1 || (a.1 == b.1 && decide (a.2 < b.2))
def first (m : Machine) (r : Req) : Int := ((m.tickets.find? (·.id == r.id)).map (·.first)).getD m.now
def aheadOf (m : Machine) (r : Req) : List Ticket :=
  m.tickets.filter fun t => t.id != r.id && !held m t && before (t.first, t.id) (first m r, r.id)
def head (m : Machine) (r : Req) : Option Ticket :=
  (aheadOf m r).foldl (fun a t => match a with
    | none => some t
    | some h => if before (t.first, t.id) (h.first, h.id) then some t else some h) none

def endOf (m : Machine) (c : Claim) : Option Int := c.est.map fun e => max m.now (c.start + e)
def events (m : Machine) : List Int := m.now :: m.claims.filterMap (endOf m)
def released (m : Machine) (τ : Int) : Int × Int :=
  let g := m.claims.filter fun c => (endOf m c).any (· ≤ τ)
  ((g.map (·.cores)).sum, (g.map (·.mem)).sum)
def fitsAt (m : Machine) (h : Ticket) (τ : Int) : Bool := match h.cores with
  | some c => c ≤ freeC m + (released m τ).1 && h.mem ≤ freeM m + (released m τ).2
  | none => m.claims.all fun c => (endOf m c).any (· ≤ τ)
/-- The head's estimated start. -/
def shadow (m : Machine) (h : Ticket) : Option Int := ((events m).filter (fitsAt m h)).min?

def tooBig (m : Machine) (r : Req) : Bool := match r.cores with
  | some c => c > capC m || r.mem > capM m
  | none => !whole m
def fitsNow (m : Machine) (r : Req) : Bool := match r.cores with
  | some c => c ≤ freeC m && r.mem ≤ freeM m
  | none => m.claims.isEmpty && quiet m
/-- What a grant claims. -/
def take (m : Machine) (r : Req) : Int × Int := match r.cores with
  | some c => (c, r.mem)
  | none => (m.ncpu, m.avail)

def decide (m : Machine) (r : Req) : Answer :=
  if m.off then .off else
  if tooBig m r then .never (capC m) (capM m) else
  let bf := match head m r, r.est with
    | some h, some e => (shadow m h).any (m.now + e ≤ ·)
    | _, _ => false
  if fitsNow m r && ((aheadOf m r).isEmpty || bf) then .ok (take m r).1 (take m r).2
  else .wait (max 0 (freeC m)) (max 0 (freeM m)) (aheadOf m r).length

/-- The line `try` prints. -/
def Answer.line : Answer → String
  | .ok c g => s!"ok {c} {g}" | .wait a b n => s!"wait {a} {b} {n}" | .never a b => s!"never {a} {b}" | .off => "off"

def grant (m : Machine) (r : Req) : Machine :=
  { m with claims := m.claims ++ [⟨(take m r).1, (take m r).2, m.now, r.est⟩],
           tickets := m.tickets.filter (·.id != r.id) }

/-- The ledger `try` leaves: a grant adds the claim and drops the ticket; a wait writes the ticket; never and off
drop it. -/
def after (m : Machine) (r : Req) : Machine :=
  let rest := m.tickets.filter (·.id != r.id)
  match decide m r with
  | .ok .. => grant m r
  | .wait .. => { m with tickets := rest ++ [⟨r.id, first m r, r.cores, if r.cores.isSome then r.mem else 0⟩] }
  | _ => { m with tickets := rest }

/-- `h` is the machine's head: a live ticket, not held, before every other live ticket that is not held. -/
def head0 (m : Machine) (h : Ticket) : Prop :=
  h ∈ m.tickets ∧ held m h = false ∧
  ∀ t ∈ m.tickets, t.id ≠ h.id → held m t = false → before (h.first, h.id) (t.first, t.id) = true

/-- What the script's own checks guarantee of its input: no negative size, a sized request of at least a core, a
machine with a core, available memory within the total, tickets named by distinct file names. -/
def WF (m : Machine) (r : Req) : Prop :=
  1 ≤ m.ncpu ∧ 0 ≤ m.total ∧ 0 ≤ m.busy ∧ 0 ≤ m.avail ∧ m.avail ≤ m.total ∧
  (∀ x ∈ m.cap.1, 0 ≤ x) ∧ (∀ x ∈ m.cap.2, 0 ≤ x) ∧ 0 ≤ m.res.1 ∧ 0 ≤ m.res.2 ∧
  (∀ c ∈ m.claims, 0 ≤ c.cores ∧ 0 ≤ c.mem ∧ ∀ e ∈ c.est, 0 ≤ e) ∧
  (∀ t ∈ m.tickets, (∀ x ∈ t.cores, 0 ≤ x) ∧ 0 ≤ t.mem) ∧ (m.tickets.map (·.id)).Nodup ∧
  (∀ x ∈ r.cores, 1 ≤ x) ∧ 0 ≤ r.mem ∧ (∀ e ∈ r.est, 0 ≤ e)

/-- The cap and reserve files, for the reserve theorems. -/
structure Files where
  cap : Option Int × Option Int
  res : Int × Int
  off : Bool
def setReserve (f : Files) (c g : Int) : Files := { f with res := (c, g) }
def setCap (f : Files) (c g : Option Int) : Files := { f with cap := (c, g) }
```

`Claims/Ledger.lean` uses `Admit.lim` for `limit_*`, and `held` for the rendering and `--json`, so the shown room is
the model's.

### 6.2 Theorems: `claim/Claims/Proofs.lean`, namespace `Claims.Proofs`

Checked by `claim/check.sh` (no `sorry`, `native_decide` or axioms beyond Lean's three). `WF m r` is a hypothesis
wherever a sign matters.

Must:

1. `decide_ok_iff`: the rule, stated whole.
   `decide m r = .ok c g ↔ m.off = false ∧ tooBig m r = false ∧ fitsNow m r = true ∧ (c, g) = take m r ∧
   (aheadOf m r = [] ∨ ∃ h e s, head m r = some h ∧ r.est = some e ∧ shadow m h = some s ∧ m.now + e ≤ s)`
2. `off_iff`: `decide m r = .off ↔ m.off`; `never_iff`:
   `decide m r = .never a b ↔ m.off = false ∧ tooBig m r = true ∧ a = capC m ∧ b = capM m`.
3. `grant_within` (the existing invariant, with backfill, the reservation and exclusive claims):
   `WF m r → decide m r = .ok c g → cc m + c ≤ limC m ∧ cc m + c + outside m ≤ m.ncpu ∧ cm m + g ≤ limM m ∧ g ≤ m.avail`;
   with `lim_bounds`, `cc (grant m r) ≤ capC m`. (For an exclusive grant `limC m = m.ncpu` and `limM m = m.total`.)
4. `no_history_no_backfill`: `r.est = none → decide m r = .ok c g → aheadOf m r = []`.
5. `unknown_shadow_no_backfill`: `head m r = some h → shadow m h = none → ∀ c g, decide m r ≠ .ok c g`.
6. `backfill_no_delay`: a grant past a head, sized or exclusive, does not move the head's estimated start later.
   `WF m r → head m r = some h → decide m r = .ok c g → ∃ s s', shadow m h = some s ∧ shadow (grant m r) h = some s' ∧ s' ≤ s`.
   (`≤`, not `=`: in the model a new claim explains measured busy cores, so `outside` can only shrink.)
7. `head_runs_by_shadow` (no starvation, under stated assumptions): the head is granted on its first try at or after
   its shadow, if every claim that was to end by then did, and nothing outside the ledger took room.
   Given `WF m r`, `head0 m h`, `shadow m h = some s`, and a later state `m'` with: the same `ncpu total cap res`,
   `m'.off = false`, `s ≤ m'.now`; `m'.claims` a sublist of `m.claims.filter (fun c => ¬ (endOf m c).any (· ≤ s))`
   (estimates held, and every claim granted in between, a backfill, ended by `s` by 6's condition);
   `outside m' ≤ outside m`; `m'.avail ≥ m.avail + (released m s).2`; `head0 m' h`. Then for any `e`,
   `decide m' ⟨h.id, h.cores, h.mem, e⟩ = .ok (take m' ⟨h.id, h.cores, h.mem, e⟩).1 (take m' …).2`.
   (For an exclusive head the filter is empty, so `m'` has no claim, and `held m h = false` gives `quiet`.) The trace
   form, "finitely many arrivals → the head is eventually granted", follows from 6 and 7 informally; it is not asked.
8. Held tickets block no one:
   - `held_not_ahead`: `held m t = true → t ∉ aheadOf m r`, hence `head m r ≠ some t`.
   - `excl_waiting_blocks_none`: `t.cores = none → (m.res ≠ (0, 0) ∨ 0 < outside m ∨ whole m = false) →
     t ∉ aheadOf m r` (the exclusive case of the above, stated in its terms).
9. Exclusive claims:
   - `excl_grant`: `r.cores = none → decide m r = .ok c g → m.claims = [] ∧ m.res = (0, 0) ∧ outside m = 0 ∧
     c = m.ncpu ∧ g = m.avail ∧ whole m = true`.
   - `excl_alone`: `WF m r → m.ncpu ≤ cc m → ∀ c g, decide m r ≠ .ok c g` (nothing runs beside an exclusive claim).
   - `excl_shadow_some`: `t.cores = none → (∀ c ∈ m.claims, c.est.isSome) → shadow m t ≠ none` (once only claims
     stand in its way and they have estimates, its start is known, so backfill goes on past it).
10. Reserve and cap arithmetic:
    - `lim_bounds`: `0 ≤ cap → 0 ≤ size → 0 ≤ lim cap size res ∧ lim cap size res ≤ size ∧ lim cap size res ≤ cap`;
      hence `0 ≤ limC m ≤ m.ncpu` and `limC m ≤ capC m` under `WF` (likewise memory).
    - `lim_zero`: `lim cap size 0 = min cap size`.
    - `lim_antitone`: `res ≤ res' → lim cap size res' ≤ lim cap size res`.
    - `reserve_restores`: `f.res = (0, 0) → setReserve (setReserve f c g) 0 0 = f`.
    - `reserve_keeps_cap`: `(setReserve f c g).cap = f.cap`; `cap_keeps_reserve`: `(setCap f c g).res = f.res`.
11. `script_*`: each of 1-9 that is about `decide` restated for the shipped script through the assumption of §7
    (`ScriptAdmits run → run m r = .ok c g → …`), so `claim/Audit.lean` lists them under it.

Stretch:

12. `shadow_some`: every claim has an estimate and a sized head fits an emptied ledger
    (`c ≤ freeC m + cc m ∧ h.mem ≤ freeM m + cm m`) → `shadow m h ≠ none`. Says when 7 applies.
13. `after_ledger`: `after` is the ledger the script leaves (the claim count rises by one exactly on `ok`, a ticket
    exists for `r.id` exactly on `wait`), stated over `after`; the differential test checks the files.

And of the history, in swarm (a `#guard`-checked pure function, proved if cheap): `estimate` is `none` iff there is no
`run` row with `wall_s > 0`, it is one of those walls, and with fewer than 10 such rows it is the largest.

## 7. Tying the script to the model

Without this the theorems are about a function the binary never runs. Two tests, both required, in a `claims_spec`
group of `claim-tests` (`claim/Tests/Spec.lean`), and one assumption in `claim/Claims/Assumptions.lean`:

```lean
/-- The shipped script's admission, assumed and tested, not proved: on a machine and ledger that read as `m`
(after `clean`, under the lock), `try` prints `(Admit.decide m r).line` and leaves `Admit.after m r`
(claims_spec: admit_awk, script_try). -/
def ScriptAdmits (run : Admit.Machine → Admit.Req → Admit.Answer) : Prop :=
  ∀ m r, Admit.WF m r → run m r = Admit.decide m r
```

`claim/check.sh` refuses the build if either case is missing.

- **`admit_awk`**: 2000 cases from a fixed-seed generator (an LCG in the test; no randomness between runs), each run
  as `LC_ALL=C awk -v … ADMIT_AWK` with the case's `c`/`q` lines on stdin; its one line must equal the model's
  `Answer.line`. The generator draws small numbers so the interesting regions are dense: `ncpu` 1-12, `total` and
  memory in units of 1024 KiB up to 16, `avail` 0-`total`, `cap` none in 1 of 2 else 0-14, `res` `(0, 0)` in 1 of 2 else
  each 0-14, `busy` 0 in 1 of 2 else 0-`ncpu*100` hundredths, `off` 1 case in 20, 0-4 claims (cores 1-6, `start`
  `now-120..now`, `est` none in 1 of 3 else 1-200), 0-4 tickets (exclusive in 1 of 5) with ids from a pool of 5 and
  `first` `now-5..now` (ties in `first` happen), the requester's id sometimes one of the tickets', its `cores` none
  (exclusive) in 1 of 5 else 1-9, `est` none in 1 of 3. The test also counts, by the model: backfill grants (`ok`
  with a non-empty `aheadOf`), backfill refusals (fits, ahead, not granted), held sized tickets, held exclusive
  tickets, exclusive grants, backfill grants past an exclusive head, `never`, `off`; it fails if any count is under
  20: a generator that drifted away from a region would otherwise pass silently. A mismatch prints the case as Lean
  and as the awk command line.
- **`script_try`**: 60 of those cases through the whole script against a scratch `SWARM_COMPUTE_DIR`: the test writes
  `cap`, `reserve`, `off`, each claim as a file with holder `t<now+100000>` (live, as `clean` reads it) and `~est`
  when it has one, each ticket as a fresh file (`all 0` for an exclusive one), a stat file with `ncpu` cpu lines, a
  meminfo file, and runs `try` with `SWARM_COMPUTE_NOW`, `SWARM_COMPUTE_BUSY` (the hundredths as `%.2f`),
  `SWARM_COMPUTE_STAT`, `SWARM_COMPUTE_MEM`. It checks the answer and the files left against `Admit.after`: claims as
  `(cores, mem, start, est)` multisets, tickets as `(id, first, cores, mem)`. At least 10 of the 60 are exclusive
  requests. This ties `caps()` (reserve, clamping, `limc`), `all`, the claim line's `~` field and the ticket rewrite,
  which the awk test does not see.
- Not tied, and said so in the assumption's doc: the `mkdir` lock serialising tries (the 50-parallel test covers it),
  `clean`'s liveness reading, and the measurement (`/proc/stat`, `vm_stat`).

If the test and the model disagree, the model is the spec: fix the script, unless the model is wrong about something
§2-§3 decides, then fix both and say so in the PR.

## 8. Tests besides §7

`claim/Tests/Ledger.lean` (`#guard`s):
- `parseTry "ok 4 1024"`; `parseLs` of a 9-field header; a claim with `~600` has `est = some 600` and its `who`; one
  without has none; a ticket with `all` has `cores = none`.
- `render`: the reservation text and `of ~10m` (§3.1); `held by the reservation`; an exclusive waiter with its reasons.
  Existing samples gain `0 0`.
- `Admit.decide` on hand cases: the §2.2 example (8 cores, a 6-core claim ending in 90 s, an 8-core head: a 2-core
  request with est 50 is `ok 2 …`, est 200 `wait`, no est `wait`; the claim without an estimate: `wait`); a held sized
  ticket is not ahead. Exclusive: on an empty, quiet machine `ok ncpu avail`; with a claim, `wait`; under a cap of 4
  of 8, `never`; an exclusive head behind a 6-core claim ending in 90 s lets a 2-core est-50 request through and holds
  an est-200 one; with `res = (1, 0)`, or `busy` past the noise floor, the exclusive ticket is held and a younger
  2-core request **without** an estimate is granted; with an `ncpu`-core claim live, a 1-core request waits.

`claim/Tests/Script.lean` (the script, a scratch dir; the `try_` helper gains the `-` estimate):
- Backfill through the script: the same example with files, then the 2-core claim's line has `~50`.
- An old claim line without `~` blocks backfill only when the head needs its cores.
- Reserve: `reserve 4 0` on an 8-core machine: a 6-core request waits held and a younger 2-core one is granted past
  it; `reserve 0 0` and the 6-core one is granted. Separately, `cap 6 -`, `reserve 4 0`, `reserve 0 0` leaves the
  `cap` file `6 -`.
- Exclusive: `all` waits for an empty ledger and gets `ok 8 <avail>`, its claim line `8 <avail> …`, its waiting
  ticket `… all 0 …`; `all` under `cap 4 -` is `never`; `try` of 0 cores is `bad size`.
- The existing cases, moved, keep passing with the new `try` argument and `ok` line (`never_off_and_all`'s `all`
  part becomes the exclusive one above).

`claim/Tests/Cli.lean` (the `claim` binary, cwd a scratch dir that is no git repo, no `SWARM_DB`):
- `claim run --cores 2 -- 'echo $SWARM_CORES nice=$(nice)'` prints `2 nice=19`, exits with the command's code, leaves
  no claim; it waits while the ledger is full and runs when a claim is dropped; 255 when nothing can fit.
- `claim reserve here 3 --mem 2`: `claim --json here` has `reserve_cores` 3, `reserve_mem_kb` 2097152, `limit_cores`
  5 and only `here`; the text says `3 reserved`; `reserve here 0` lifts both; a negative or non-number and an
  unknown machine `die`. `claim op here ls` prints the 9-field header.
- `claim run --cores all --mem 1 -- true` is refused.

swarm's `Tests/Cli/Compute.lean`:
- `swarm compute reserve here 3` and `swarm compute --json` show the same as `claim`.
- `swarm run` with history: the claim line has `~<the 90th percentile>`; stderr says `~Nm`; with 12 `run` rows of
  walls 1..12 s the estimate is 11, and a `swarm` row of 1000 s in the window does not change it.
- `swarm run --cores all -- 'echo $SWARM_CORES'` prints the machine's 8; the stderr line says `the whole machine`.
- `swarm run -- 'echo nice=$(nice)'` prints `nice=19`; where `ionice -c3 true` works, `ionice -p $$` in the job says
  `idle`. The remote case (fake hc's `laptop`) prints `nice=19` too.
- A local `swarm run -- true` leaves a `source='run'` row with its wall time (under a minute) keyed by `true`; a remote
  one with a `run.prefix` is keyed by the user's command.

swarm's `Tests/Compute.lean` and `Tests/Cost.lean`:
- `estimate`: none for `[]`, for rows with `wall_s = 0` and for rows of other sources; nearest-rank p90 otherwise
  (walls 1..10: 9; 1..4: 4; 1..50: 45).
- `recordSql` keeps a 5 s `run` row and drops a 5 s `swarm` row; 25 rows of one key all stay (no pruning; the
  pruning cases change accordingly).

`herdr/rail-test.mjs`: `splitOf` with `limit_cores`/`limit_mem_kb`; `whyOf` of a held and an exclusive waiter.

## 9. Docs and other places to change

- `sw-compute.md`: §1's `grant iff` line and §2's table point here; §7's "Priorities" bullet says backfill is in
  (no daemon) and "A proof" bullet points to §6-§7; a line at the top says the code is the `claim` tool.
- `DESIGN.md` decision 6 and "Resources by information, not gates": claims may start past a waiting head when their
  history says they end before it can start; `--cores all` is exclusive; the user's reservation; jobs at the lowest
  priority, `nix build`'s daemon not included. "What's built": compute claims are the `claim` tool, which swarm uses;
  it knows nothing of swarms.
- `SKILL.md` item 6: `claim` (and `swarm compute`) `reserve <machine|here> <cores> [--mem G]`, `reserve … 0` lifts it;
  cap is the standing limit, reserve the temporary one; `--cores all` for a benchmark that needs the machine alone.
- `brief.md` heavy work: jobs run at the lowest priority; a job with history may start before older waiters when it
  will end before they can start (nothing to do); `--cores all` only for a benchmark.
- `cmd-cost.md`: `run` rows have no threshold, there is no pruning, the `cmd_rk` index, the 50-row window and the
  estimate; `swarm cost` and the note include short jobs.
- `OpsHelp.lean`: `helpRun` (the estimate, `all`, the priority), `helpCompute` (`reserve`, a machine argument).
  `claim -h` and each subcommand's `-h` are the tool's docs besides this file.
- `research/sw-compute-view.md` and `herdr/mods/rw-rail/tree.js`: `splitOf` uses `limit_cores ?? cap_cores` (and
  memory) where it uses the cap for free room, so the panel's free matches admission under a reservation; `whyOf`
  says `held by the reservation` for a held sized waiter and the exclusive reasons (§3.1) for a held exclusive one, and
  `waits for an empty machine` for an exclusive one that is not held. The panel's reserve control is not in this step.

## 10. Not in this step

- A declared duration on `swarm run` (`claim run --est` has one).
- Protecting more than the head (Slurm's later reservations), and the "extra room" rule (a job running past the
  shadow on room the head does not need).
- Learning estimates per core count, or comparing a job's estimate with its wall time in the footer.
- Measuring a local job's CPU and peak in its own `run` row.
- The trace theorem of no starvation (§6.2, 7).
- A model of `clean`, the lock or the measurement.
- Priority for `nix build`'s daemon builds; enforcement (cgroups).
- The Noctalia plugin itself, and a reserve control in the Herdr panel.
- Renaming the ledger directory and the `SWARM_COMPUTE_*` variables.
- **A daemon.** The user's direction is a daemon later, for fairness between swarms and CI scheduling. This design is
  meant to be taken over, not rewritten:
  - It keeps the op interface (`try drop ls cap reserve off on`, their arguments and output lines) as its protocol,
    with `Claims.call` the only place clients change; the files (claims, tickets, `cap`, `reserve`, `off`) as its
    state, so it can start from a ledger the script wrote, and the script can stand in when it is down, both under
    the same `mkdir` lock; and `Claims.Admit` with its theorems, run compiled rather than through awk (so for the
    daemon `ScriptAdmits` and the differential test fall away). The `claim` package is already the unit it would ship
    in.
  - It replaces polling (a waiter retries every 5 s, a ticket is stale after a minute) with waiters told on a socket;
    pid and `t<epoch>` liveness with connection liveness; the 0.5 s sample per call with continuous sampling; and
    the order. `before` (first, then id) is the one place the queue order is defined, so fairness between swarms or a
    CI priority is a new `before`. Theorems 1-9 hold for any order; who becomes the head, and when, becomes the
    policy's question.

## 11. The user's decisions (2026-11-15) and what is still open

Decided:
1. `swarm run` records every job in cmd-cost without a threshold (§2.1); `swarm cost` and the note include short jobs.
2. No pruning; the estimate is the 90th percentile of a recent window, the largest below 5 rows; `size` reads the
   same window (§2.1).
3. `--cores all` is exclusive (§2.4), held while the reservation or unclaimed use keeps it off.
4. `reserve` without `--mem` reserves no memory.
5. Older binaries ignoring the `reserve` file: accepted; every machine is upgraded on landing.
6. The Herdr rail panel change is in (§9).
7. The name is `claim`; the ledger directory and `SWARM_COMPUTE_*` keep theirs.
8. A separate Lake package at `claim/` (§1a).

Chosen here, for the user to overturn:
- The window is 50 rows (§2.1).
- An exclusive request under a cap below the machine is `never`, not "the cap's share alone" (§2.4).
- The estimate reads only `run` rows of the window, and a local `run` row carries no CPU or peak (§2.1).
- `claim run` does not read cmd-cost even inside a repo (§1a).

## 12. Build plan

**Sonnet build**, two PRs, each with both `check.sh` green; §6.2's theorems and §7's assumption and cases are the
proof pass's.

PR 1, the extraction, with no change in behaviour:
1. The `claim/` package (§1a): `lakefile.lean`, `lean-toolchain`, `Claims/Util.lean`, `Host`, and the moves of the
   table (`Ledger`, `Machines`, `Acquire`, `Cli`), with `swarm compute` and `swarm run` calling them through a
   `Host` built from swarm's classes; `require claim` in `swarm/lean/lakefile.lean` and `hpl/lakefile.lean`, the
   manifest.
2. `Main.lean` and `lean_exe claim`: `claim op`, the show, `cap`, `off`, `on` and `run`.
3. `claim/build.sh`, `claim/check.sh`, `claim/Audit.lean` (the axiom gate; the assumption part with no assumption
   yet), the `claim/claim` launcher; swarm's `build.sh` and `check.sh` calling claim's; `swarm/swarm`'s `find`;
   `install.sh`'s link; the flake (`claim` derivation, `packages.claim`, the default env, both toolchains checked).
4. The script cases and ledger `#guard`s moved to `claim/Tests/`, `claim-tests` with its `--list`; `claim/Tests/Cli`
   cases of `claim run` and `claim op` from a non-repo cwd. Every existing test passes.

PR 2, the features, on top:
1. cmd-cost (§2.1): `recordSql`'s gate and no pruning, the `cmd_rk` index, `history`'s window, `estimate`,
   `predict`'s window; `run` rows for local jobs and the user's-command key.
2. `claim/Claims/Admit.lean`: the §6.1 definitions exactly, `after` included, and the `#guard`s of §8.
3. The script (§5): `caps()` with the reservation, `ADMIT_AWK` (backfill, exclusive, held), `try`'s new argument,
   `ok`'s memory, the file writes, `reserve` op, `ls`'s header, the two hooks, `LC_ALL=C`, the 0-core refusal.
   `parseTry`, `parseLs`, `Claim.est`, `Ticket.cores`, `Ls` fields, `render`, `json`.
4. `Run.lean`: the estimate into `try`, the granted memory into the environment, the stderr line, `all` without
   `--mem`; `lowPrio` here and remote (§4), and in `claim run`.
5. `Claims/Cli.lean`: `reserve`, the one-machine form, `claim run --est`; `OpsHelp` and `claim -h`.
6. §8's tests; §9's docs and the `tree.js` change with its rail test.

**Opus proof pass** (after PR 2 merges, on its own branch, in `claim/`):
1. `Claims/Proofs.lean`: §6.2's must theorems, then the stretch ones.
2. `ScriptAdmits` in `Claims/Assumptions.lean`, `claim/Audit.lean`'s tag check against `claim-tests --list`, and
   §7's two `claims_spec` cases in `claim/Tests/Spec.lean` with the generator and its coverage counts.
3. Fix what either finds (§7's last paragraph), and run `swarm/lean/check.sh` (which runs claim's) on both binaries.

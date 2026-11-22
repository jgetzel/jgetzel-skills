# sw-compute: sized claims on cores and memory, across machines and swarms

> The code is the `claim` tool (`claim/`, a Lake package of its own; `swarm compute` is `claim`). Backfill past a waiting
> head, `--cores all`, the user's reservation, jobs at the lowest priority and the admission model changed §1's grant
> rule and §2's ops: [sw-compute-backfill.md](sw-compute-backfill.md).

Decided with the user 2026-11-14. Replaces DESIGN decision 6's "no slots, no queues" for jobs started through
`swarm run`; "never deny a Bash command" stays. `swarm heavy` failed because it counted jobs (two or three slots)
instead of sizing them. Here every job claims a number of cores and an amount of memory.

Alternatives weighed and dropped: systemd units as the ledger (no macOS), one scheduler daemon (always-on process,
heartbeats, lease timeouts), Nomad (a cluster on four machines, places on declared usage only, `swarm run` would still
do the sync, wait, sizing and recording).

## 1. The model

- **A ledger on each machine**, per user: `${XDG_STATE_HOME:-$HOME/.local/state}/swarm-compute/`. It belongs to the
  machine, not to a repo or a swarm, so every swarm and every controller machine sees the same claims (like
  `cmd-cost`). Linux and macOS alike.
- **A claim** is one file, `claims/<id>`, one line: `cores mem_kb holder start who cmd…`. `holder` is `p<pid>` (live
  while that pid is, on that machine) or `t<epoch>` (live until then: a claim made for a job that has not started).
  No lease durations: a claim lasts as long as its job. A dead claim is deleted by whoever reads it next.
- **A ticket** is one file, `queue/<id>`, one line: `first_epoch cores mem_kb who`. A waiter touches it on every
  attempt; one not touched for a minute is stale and deleted. Tickets make the queue first-in-first-out per machine.
- **A cap** per machine: file `cap`, `cores mem_kb`, each a number or `-` (all the machine has). File `off` present:
  the machine takes no new claims; running jobs finish. Reserving cores for the user is lowering the cap.
- **Admission** is one shell script (§2) run on the target under a lock, so two claims never both take the last
  cores. A claim is granted when it fits under **both** the ledger and the measurement:

  ```
  outside    = max(0, round(busy - claimed_cores) - max(1, ncpu/8))   # use nobody claimed; max(1, ncpu/8) cores of noise ignored
  free_cores = min(cap_cores - claimed_cores, ncpu - claimed_cores - outside)
  free_mem   = min(cap_mem - claimed_mem, available_mem)
  grant iff cores <= free_cores and mem_kb <= free_mem and no older live ticket on this machine
           (now: or the request's estimated end is no later than the oldest waiter's estimated start: sw-compute-backfill.md §2.2)
  ```

  The ledger covers jobs that just started and have not ramped up; the measurement covers the user's own work and
  agents that run a build outside `swarm run`.
- The noise floor is an eighth of the machine (at least 1 core), so a dozen idle agents do not block a head-of-queue
  request for good.
- `busy` is cores in use now, not the load average (which lags a minute after a big job ends): Linux, two reads of
  `/proc/stat`'s first line 0.5 s apart, `ncpu * Δnon-idle / Δtotal`; macOS, the sum of `ps -A -o %cpu` over 100.
  Sampled before the lock is taken. `available_mem`: `MemAvailable`, or macOS free + inactive + speculative +
  purgeable pages (as `Machine.darwinMem`).
- No enforcement in this step. A job is told its cores through its environment (§3). Follow-up, Linux only: start the
  job in a `systemd-run --user --scope -p CPUQuota=<cores>00%`, and a quota on each agent's own scope.

## 2. The script

One POSIX `sh` script, a string constant in `SwarmLean/Lib/Compute.lean`, run as `sh -c SCRIPT sh <op> <args…>`: here
directly, on another machine through `hc exec --on <m> --timeout 20` (as `Run.remoteTick` does). No `swarm` binary,
`sqlite3` or `flock` on the target; only `sh`, `awk`, `mkdir`, `find`, `ps`, `kill`, `date`, and `sysctl`/`vm_stat` on
macOS.

- Lock: `mkdir $d/lock`, the holder's pid in `lock/pid`; a waiter retries every 0.1 s and removes a lock over a minute
  old whose pid is dead or unwritten (a younger one may have been taken just after the waiter read the pid). Released
  by a trap on exit.
- Every op first deletes dead claims and stale tickets.

| Op | Does | Prints |
|---|---|---|
| `try <id> <cores\|all> <mem_kb> <est_s\|-> <holder> <who> <cmd>` | admission (§1, with backfill, sw-compute-backfill.md §2-§5); writes the claim and removes the ticket, or rewrites the ticket | `ok <cores> <mem_kb>`, `wait <free_cores> <free_mem_kb> <ahead>`, `never <cap_cores> <cap_mem_kb>` (larger than the cap), or `off` |
| `drop <id>` | removes the claim and the ticket | |
| `hold <id> <pid\|t>` | makes `p<pid>` the claim's holder, the rest of its line kept; `t` starts a timed holder's 15 minutes again (`t<now + 900>`) and keeps a `p` holder; exit 3 when the claim is gone (lapsed, its holder dead, or dropped) | |
| `ls` | | `ncpu busy total_kb avail_kb cap_cores cap_mem_kb off reserve_cores reserve_mem_kb`, then `c <claim line>` and `q <ticket line>` rows |
| `cap <cores\|-> <mem_kb\|->` | writes `cap` | |
| `reserve <cores> <mem_kb>` | writes `reserve` (`0 0` removes it): the user's reservation | |
| `off`, `on` | makes or removes `off` | |

`all` is the whole machine, alone (sw-compute-backfill.md §2.4); it was the cap. `<holder>` is `p<pid>` or `t`, which the script turns into `t<now + 900>`.

## 3. `swarm run`

```
swarm run [--on <machine>] [--cores N|all] [--mem <G>] [--env NAME[=VAL]]... -- <cmd…>
```

1. **Size.** `--cores` and `--mem` when given. Else from the cmd-cost rows for this repo and command key on any
   machine: cores = 2, or the largest `cpu_s / wall_s` rounded up over rows with `cpu_s > 0` and `source != 'run'`
   (those rows hold a %CPU sample, and many rows have no CPU reading), whichever is more, so history only raises the
   default; memory = the largest `peak_kb` × 1.25 over every row. With no history, 2 cores and 2 GiB. One stderr line says what was claimed and from what.
2. **Candidates.** `--on m`: only `m`. Else this machine, then `.claude/swarm.json` `run.machines` in order (a list
   of `hc machine ls` names; absent: this machine only, as before). A machine not `connected` is skipped.
3. **Claim.** `try` on each candidate in order; the first `ok` wins and `drop` runs on the others. If none: one stderr
   line with each machine's free cores and memory, then again every 5 s, silently, every machine each round (one that
   did not answer is tried again). Exit 255 with a message naming each when the first round has no `wait` answer, or
   when in a later round every candidate answered `never` or `off`; a round where a machine did not answer keeps waiting. There is no timeout; the agent runs this in the
   background and can kill it.
4. **Run.** Here: holder `p<swarm run's pid>`, `drop` after the command. On another machine: holder `t`, then the
   sync, then the job script's first step is `hold <id> $$` and its exit trap `drop <id>`. `hold <id> t` renews the
   claim before the sync, every 5 minutes while rsync runs, and after it (board #126), so a long first sync keeps it; a
   claim that lapsed anyway fails that renewal or the job's `hold`, and the job never runs, saying so (board #109). A `--detach` run here `hold`s its
   claim for the background process the same way.
   A failed sync or `hc run` drops the claim.
5. **Environment** the job gets: `SWARM_CORES`, `SWARM_MEM_KB`, `MAKEFLAGS=-j<cores>`, `CARGO_BUILD_JOBS`,
   `NIX_BUILD_CORES`, and `NIX_CONFIG` with `cores = <n>` and `max-jobs = 1` appended (a `nix build` runs in the nix
   daemon, which only obeys these for a trusted user). `{cores}` is substituted in `run.set` and `run.prefix`, as
   `{dir}` is, for tools with their own flag. A value the caller or `run.set` gives wins.
6. **Record.** `job-start` gains `cores`, `mem_kb`, and the machine chosen; `job-end` gains `wait_s`. The footer says
   `waited 2m10s` when it did. `wait_s` is the signal the auto-spawner will read later.

## 4. `swarm compute`

- `swarm compute [--json]`: this machine and every hc machine, from `ls`:

  ```
  here: 8 of 20 cores claimed (cap 20 of 24, 9.3 busy), 10.0 of 80.0G claimed (61.2G available)
    sr-3   6 cores  8.0G  4m  nix build .#x
    sr-5   2 cores  2.0G  1m  cargo test
    waiting: sr-7 12 cores 2.0G 2m
  desktop: off
  mini: disconnected
  ```
- `swarm compute cap <machine|here> [--cores N|all] [--mem G|all]`, `swarm compute off|on <machine|here>`.

## 5. Tests

- The script alone, against a scratch `XDG_STATE_HOME`: 50 parallel `try` of 2 cores under a cap of 8 grant exactly
  4 (as `test-claim.sh` does for task claims); a claim with a dead pid or a past `t` is not counted; an older ticket
  holds back a younger, smaller request; `never` and `off`; `all` waits for an empty ledger.
- `swarm run` in `Tests/Cli` with the fake `hc`: routes to the second machine when the first is full, waits and then
  runs when a claim is dropped, exit 255 when nothing can ever fit, the job's environment, the claim gone after the
  job and after a killed job.
- The sizing from history and the `ls` rendering as pure functions with `#guard`s.
- The script's macOS branch can't run in CI here: keep it to `sysctl`, `vm_stat`, `ps` and `awk`, and test its
  arithmetic by feeding the awk programs recorded output (`Tests/Run.lean` has a `vm_stat` sample).

## 6. Docs to change

- `DESIGN.md`: decision 6 and "Resources by information, not gates" say what is now claimed and what is still only
  information.
- `brief.md`: heavy work goes through `swarm run` (`--cores`, `--mem`); it waits for room and may run elsewhere.
- `swarm/SKILL.md`: `run.machines`, `swarm compute`, the caps. `swarm/research/sw-remote-jobs.md` §5 "Picking a machine" points here.
- `OpsHelp.lean`: `run`'s and `compute`'s help.

## 6a. As built, where it differs from the above

- Test hooks: the script reads `SWARM_COMPUTE_STAT` and `SWARM_COMPUTE_MEM` (files standing for `/proc/stat` and
  `/proc/meminfo`) and `SWARM_COMPUTE_DIR` (the ledger's directory; the screenshot sandbox's "desktop"), `swarm run` reads `SWARM_COMPUTE_POLL_MS` (default 5000).
- The script's `cap` takes `=` for a field to keep; only `try` and `ls` take the lock and clean.
- 5. A machine that does not answer counts as no room for the decision above, and is tried again each round.
- 6. The sizing key is the user's command (not the prefixed one); `--mem` is decimal GiB; the stderr line says
  `from the history`, `no history: the default` or `as asked`.
- 7. A job's wall time starts after the claim; the claim comes before the job id and `job-start`, so a waiting job has
  no event; the footer shows `waited NmSSs` from 1 s.
- 8. `swarm compute` ages use the controller's clock against the machine's claim start; a machine that is `off` with
  nothing on it renders as `name: off`.
- 9. `run.set` is still applied to remote jobs only; `{cores}` in `run.prefix` applies to both.

## 7. Not in this step

- Enforcement (cgroup quotas), §1.
- Fairness between swarms, preemption: the point at which a scheduler daemon or Nomad is the answer. Backfill is in, still
  with no daemon (sw-compute-backfill.md §2), and jobs run at the lowest CPU and I/O priority (§4 there).
- The machine note. (The Herdr panels showing claims: swarm/research/sw-compute-view.md, board #189.)
- A proof. Admission is decided by the script, so "claims never exceed the cap" is tested (§5), not proved; the model
  and the theorems, and how the script is tied to them, are sw-compute-backfill.md §6-§7.
- What the job actually used against what it claimed, in the footer.
- The auto-spawner reading `wait_s`.

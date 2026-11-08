# sw-remote-jobs: running heavy jobs on other machines

Task #44. What a typical per-repo "run it on the laptop" script does, what
of it is generic, and one recommended shape for running a build or test on
another machine from a swarm agent. Research only; nothing here is built yet.

Measured 2026-11-08 between two machines (a desktop and a laptop with twice
its cores) joined as one hc machine (`hc machine ls`: `laptop`, target
`user@laptop`, hc 0.1.16). The example repo below is called `app`: a Rust
workspace with browser e2e specs, worked by many swarm lanes (`app-1`,
`app-2`, …). Probe dirs made on the laptop were removed.

## 1. The pattern today

A repo-local script, `run-remote.sh <cmd…>`, run from a lane's worktree:

1. `ssh laptop mkdir -p ~/remote/app/<lane>`.
2. `rsync -rlpD --checksum --delete --exclude=.git --filter=':- .gitignore'`
   the worktree there. By content, and without `-t`, so a sent file takes
   the laptop's clock: an edit older than the laptop's last build would
   otherwise look older than the artifact and cargo would test stale code.
3. Picks env vars to forward: a few name prefixes (`APP_*`, `TEST_*`) plus
   every `process.env.X` that a spec file reads. The second part exists
   because agents' scratch-spec knobs were silently dropped before it.
4. `ssh`: `git init` + `git add -A` in the copy (nix flakes see only tracked
   files; the index also marks what the job writes), then
   `<env> CARGO_TARGET_DIR=~/.cache/app-target/<lane> nix develop -c
   ~/app/scripts/heavy.sh <cmd>`, where `heavy.sh` is the repo's wrapper
   (nice, a share of the cores, a shared compile cache, no slots).
5. Brings back a screenshots dir outside the tree, `test-results/`, and
   every file the job changed or created in the tree (`git ls-files -m -o`).
6. Exits with the command's code.

Agents usually learn of such a script only from its own header.

## 2. Measurements

| What | Result |
|---|---|
| `ssh laptop true`, new connection | 0.48 / 0.50 / 0.54 s |
| same with `ControlMaster` reuse | 0.58 first, then 0.04–0.09 s |
| `hc exec --on laptop true` | 0.11–0.17 s |
| `hc run --on laptop true` (a new terminal) | 0.12–0.18 s; `exit 3` comes back as 3 |
| rsync of a worktree (870 files, 63 MB), cold | 2.9 s |
| same, warm, nothing changed (`--checksum`) | 0.49–0.70 s (one 2.4 s while the laptop was loaded) |
| same, one file changed | 0.59 s, 1 file sent |
| warm without `--checksum` | all 870 files resent: no `-t`, so mtimes never match. Intended (step 2) |
| rsync with `-e 'hc exec --on laptop -i'` | hangs; killed at 30 s. `hc exec -i` is not a duplex stream |
| `hc run` of a 50,000-line job, foreground | printed 1,120 lines; `hc read` afterwards started at line 49,881 |
| `hc run --rm` | in one of two runs the output was gone before it printed |
| `hc get <t> --json` on a finished job | `labels`, `argv`, `cwd`, `created_ms`, `finished_ms`, `exit_code`, `reason` |

Per job the script opens 7 ssh connections, about 3.5 s of handshakes; the
sync itself is under a second warm. Neither matters next to a cargo build,
but they add up for a 20 s single test.

What the pattern leaves behind, in general:

- **Disk.** One sync dir and one target dir per lane, on the laptop, that
  nothing removes when the lane lands. With many lanes and Rust target dirs
  this reaches hundreds of GB.
- **Wrapper drift.** The wrapper runs from the laptop's own checkout, which
  is only as fresh as the last time someone pulled there.

And on the agent's machine:

- A `run-remote.sh cargo test` call matches `HEAVY_RE` (`cargo test`), so
  the hook logs `heavy-start` and shows the **local** machine note: the
  wrong machine's memory at the moment the agent chose.
- `heavy_procs` sees only a local `ssh` process, which no pattern matches.
  Remote jobs are invisible to the note, the panel and `watchd`.
- `heavy-start` keeps 80 characters of the command, which often starts with
  `cd <worktree> &&`, so remote use can't be counted from the event log.

## 3. What is generic and what is per repo

| Part | Generic | Per repo |
|---|---|---|
| Sync | rsync by checksum, no mtimes, `--delete`, skip `.git` and ignored files | – |
| Throwaway git index in the copy | always (flakes need it; it finds what the job wrote) | – |
| Which machine, how to reach it | `hc machine ls` (name, ssh target, state) | – |
| Env | `--env NAME[=VAL]` on the call | regexes of names to forward; files to scan for names |
| Cache dirs | one per worktree per machine | which variable (`CARGO_TARGET_DIR`) |
| Wrapper | – | the command prefix (`nix develop -c scripts/heavy.sh`) |
| Bring back | files the job wrote in the tree | extra dirs (`test-results/`, a dir outside the tree) |
| Record, cleanup, note | job events, removing a landed worktree's dirs, the other machines' load | – |

Forwarding "every variable that differs from the claude process's env"
would need no config, but measured it differs in 23 variables, including
`CLAUDE_CODE_MESSAGING_TOKEN`. Sending tokens to another machine is out, so
names stay explicit.

## 4. Options

**Where it lives.**

- **A. Keep a script per repo.** Works today. Every repo copies ~30 lines,
  nothing records the jobs, and the note shows the wrong machine.
- **B. A separate user skill** (`remote-run`). Usable without a swarm, but it
  needs its own config and its own job log, and the swarm would have to read
  both to show jobs, clean dirs and build the note.
- **C. A `swarm run` command in the swarm CLI.** The CLI already has the
  per-repo store (`swarm.db`, one per repo, so it works in any repo with or
  without a swarm), the event log, the Bash hook, the machine note, `watchd`
  cleanup and `.claude/swarm.json`. `$SWARM_NAME` is optional.

**Transport for the command.**

- **ssh.** Output streams in full; nothing to see from Herdr; 0.5 s per call.
- **`hc run --on`.** A named, labelled terminal on the laptop that the user
  can watch and attach to in Herdr; exit code, start and end times and
  labels come from `hc get`; 0.15 s. Its screen keeps only the last ~1,000
  lines and `--rm` can lose them, so the full output goes to a log file.

Files can't go over hc (rsync over `hc exec -i` hangs), so they stay on ssh,
with `ControlMaster` so each call after the first costs ~0.05 s.

**Sync.** rsync by checksum (0.5–0.7 s warm) is fine. Pushing a commit to a
clone on the laptop would need the agent's uncommitted work committed first;
no gain.

## 5. Recommendation: C, with ssh for files and hc for the command

### CLI

```
swarm run [--on <machine>] [--env NAME[=VAL]]... -- <cmd…>
```

- No `--on`: runs `<prefix> <cmd>` here, recorded the same way. A repo that
  routes heavy commands through `swarm run` gets attributable local jobs
  without `/proc` guessing (#43).
- `--on laptop`: a machine from `hc machine ls`; its `target` is the ssh
  destination, so no hosts in config.
- Prints the job's last 200 lines and one footer:
  `job j12 exit 1 on laptop, 4m12s (sync 0.6s, back 0.3s), tree 3f9c2a1; log: <path>`.
  `tree` is the copy's `git write-tree`: what was tested, for
  `task done --evidence`.
- Exit code is the command's. **255** means the job never ran or its
  machine was lost, so a red test and a sleeping laptop don't look alike.

Steps for `--on m`:

1. `hc machine ls`: `m` not `connected` → print its state, exit 255.
2. rsync (step 2 of §1, `ControlMaster` on) to
   `~/.cache/swarm-run/<repo>/<wt>/src` on `m`.
3. `hc run --on m --name <agent>-j<id> --label swarm-agent=<agent>
   --label swarm-job=<id> --label swarm-task=<n> --label swarm-wt=<wt>
   --no-notify --cwd <src> sh -c 'git init -q; git add -A; <env> <set>
   <prefix> <cmd> > <log> 2>&1'`, then `hc wait` until it ends. No `--rm`.
   The parent is the agent's terminal, so the job dies with the agent;
   whether that holds across machines is untested.
4. Bring back the log to `<git common dir>/swarm/jobs/<id>.log`, the
   `bring_back` dirs, and the files the job wrote (`git ls-files -m -o`). A
   file the agent edited locally after the sync is not overwritten: it goes
   beside the log under `jobs/<id>/` and the footer names it.
5. `hc rm` the terminal.

### Config: `.claude/swarm.json`, key `run`

All optional; with none, `swarm run --on m -- <cmd>` syncs, runs `<cmd>` in
the copy and brings back what it wrote. The example repo's would be:

```json
{
  "run": {
    "prefix": "nix develop -c scripts/heavy.sh",
    "env": ["^(APP_|TEST_)"],
    "env_scan": [["e2e/*.spec.ts", "process\\.env\\.([A-Z_][A-Z0-9_]*)"]],
    "set": {"CARGO_TARGET_DIR": "{dir}/target"},
    "bring_back": ["test-results/", "~/app-screenshots/"]
  }
}
```

- `prefix` runs from the synced tree, so the wrapper is the same version as
  the code under test, not the laptop checkout's. A wrapper that finds a
  local, ignored helper (a compile-cache link) next to itself must fall back
  to the main checkout's copy, since ignored files aren't synced.
- `{dir}` is `~/.cache/swarm-run/<repo>/<wt>`, one per worktree per machine.
- `~/` paths in `bring_back` mean the same path on both machines.

### Picking a machine: information only

- `watchd` reads each connected machine once a tick with one `hc exec --on m`
  (`/proc/loadavg`, `meminfo`, `pressure/memory`, `nproc`; ~0.15 s) and the
  live `swarm-job` terminals from `hc ls`, and stores them. The hook reads
  the stored values; it never waits on the network.
- The machine note gains one line per other machine:
  `laptop: 81/93G available, load 36 on 24 cores, jobs: sr-3 cargo test 4m, sr-5 e2e 1m`
  or `laptop: disconnected since 07:40`.
- The hook treats `swarm run` as heavy (today `NOT_HEAVY` skips any command
  starting with `swarm`) and shows the note before the job starts.
- No automatic machine choice, fallback, queue, slot or hold (DESIGN
  decision 6). The agent reads the note and picks.

### Recording

- Events `job-start` (agent, data: id, machine, hc address, worktree, task,
  command) and `job-end` (exit or `lost`, seconds, sync and bring-back
  seconds, tree). The command goes in full, not cut at 80 characters.
- `swarm state --json` gains `jobs`: started and not ended, checked against
  `hc ls` so a lost one shows as lost. That is the remote half of #43's
  "Running now".
- swarm-retro: jobs per machine, minutes, exit codes, lost jobs, sync
  overhead.

### Failure modes

| Case | What happens |
|---|---|
| Laptop asleep or offline at start | Step 1: exit 255 and the machine's state. The agent picks again |
| Laptop lost mid-job | `hc wait` fails: exit 255, footer gives the terminal (`laptop/t7`) to `hc wait` later; `job-end` says `lost` |
| Agent edits during the job | The job tests the synced snapshot; the footer's `tree` says which. Bring-back keeps local edits (step 4) |
| Two jobs from one worktree at once | Both would rsync into one `src`. The second sees the first's live `swarm-wt` terminal and syncs to `src.2`, sharing `target`; cargo's own lock orders the builds |
| Two agents, one cache dir | Can't happen: dirs are per worktree, and two agents in one worktree already get the `shared-tree` notice |
| Disk | When `watchd` removes a landed agent's worktree it also runs `rm -rf ~/.cache/swarm-run/<repo>/<wt>` on each machine its `job-start` events name |
| Wrapper drift | Gone: the wrapper comes from the synced tree |

### Lines to add

`brief.md` (agents):

> - **Other machines.** `swarm run --on <machine> -- <cmd>` runs a build or
>   test on another machine (`hc machine ls`) against a copy of your
>   worktree and brings back what it wrote. The exit code is the command's;
>   255 means the machine never ran it. The machine note shows each
>   machine's memory, load and jobs: pick by it. Nothing waits for a slot.

`SKILL.md` (communicator), under setup:

> Other machines: `hc machine add` makes one usable by `swarm run --on`.
> Repo knobs (wrapper, env, cache variable, bring-back) go in
> `.claude/swarm.json` `run`.

A repo that has its own remote script, after this lands: add a `run` block,
point its docs at `swarm run --on <machine> -- <cmd>`, delete the script.

## 6. Not decided here

- Sync and target dirs that old scripts already left on other machines:
  removing them is the user's call (another machine, not reversible).
- Whether a dead agent's terminal ends its remote child (step 3) was not
  tested. If not, `watchd`'s orphan kill extends to `hc kill` of live
  `swarm-job` terminals whose agent has ended.
- Size: about 150 lines in `swarm/swarm` plus tests with fake `hc` and
  `rsync` on `PATH`.

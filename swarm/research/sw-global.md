# sw-global: one db per machine, a swarm is a group of agents, tasks belong to no swarm

Design, 2026-11-21, against `origin/main` at f8a7946. Decided with the user; the build is the board this doc seeds.

## 1. Why

A swarm today is a db file found from the current folder: `$SWARM_DB`, else `<git common dir>/swarm/swarm.db`
(`Lib/Spawn.lean` `dbPath`, again in `Cmd/Run.lean`), pinned on top to a Herdr space (`meta.space`, `Cmd/Agents.lean`
`join`). Agents carry `SWARM_DB` in their settings, so their hooks never guess; everything else guesses from the
folder: a human's shell, the communicator, the Herdr panels (one `swarm state` per space folder, `rw-rail/main.js`).
The bugs that come from that guessing:

- an agent whose terminal is in another repo is "in another repo" (`Cmd/State.lean`), not `ours` to watchd, and held;
- an agent or the panel lands in the wrong swarm because its folder named another db;
- cross-repo work needs special cases (352a472, `Cmd/Hook.lean` "a file of another repo");
- two swarms in one repo can't exist, and a task that spans repos has no home.

And the store reads every table a transaction names in full, runs a pure `Db → Db × α`, and writes the difference back
(`Real.lean` `loadDb`/`storeDb`, `Db/Plan.lean` `dbPlan`). Hooks load the append-only `event` table on every tool call
(`Cmd/Hook.lean:106,191`). The cost grows with history and lengthens every write transaction.

## 2. The model

**One db per machine**: `$XDG_STATE_HOME/swarm/swarm.db` (else `~/.local/state/swarm/swarm.db`). `SWARM_DB` stays only
as an override for tests. No db under any git dir, no registry dir (`Lib/Spawn.lean` `registryDir`): the db is the list.

**A swarm** is a named group of agents with one communicator, one set of staffing knobs and the repos its auto-spawn
draws from. Nothing else belongs to it. **Membership is the agent row's `swarm` column**, set by `swarm join` /
`spawn`; moving an agent is one update. **Tasks, locks, conflicts, CI and worktrees belong to repos, not swarms.**

### Schema (fresh; no migration of old per-repo dbs)

| Table | Columns (new or changed in bold) | Notes |
|---|---|---|
| **`swarm`** | **`name` pk, `comms`, `created`, `ended`** | replaces `meta.comms` and the per-swarm meta keys' home |
| `meta` | **`scope`**, `k`, `v`, pk(**scope**, k) | scope = a swarm name for its knobs (`agent_min`, `rules`, `away`, `queue_only`, `reuse_below`, `ctx_*`, `spawn_*`, …); `''` for the machine (`watchd*`, `machines`, `jobs`). `space` goes. |
| `agent` | `name` pk, **`swarm`** (null: in none), … | names are unique on the machine (prefixes already make them so) |
| **`repo`** | **`path` pk** (the main worktree's toplevel, absolute), **`base`** | `base` from `.claude/swarm.json`, read when the repo is first seen |
| **`swarm_repo`** | **`swarm`, `repo`**, pk(both) | the repos a swarm's auto-spawn staffs from |
| `task` | no swarm column; **`created_by`** is who added it | |
| **`task_repo`** | **`task`, `repo`, `base`** (null: the repo's), pk(task, repo) | zero or more: a research task touches none, a cross-repo one several |
| `workspace` | **`repo`**, `path`, `branch`, `base`, `agent`, `ro` | one row per worktree; an agent on a 2-repo task has two |
| `lock` | **`repo`**, `path`, …, pk(**repo**, path) | shared by every swarm working in that repo |
| `conflict`, `pairkey`, `cursor` | unchanged | keyed by agent names, which are machine-unique |
| `ci` | **`repo`**, `id`, …, pk(**repo**, id) | |
| `msg` | `dest` may be **`@<swarm>`** besides an agent, `#task`, `@all` (= the sender's swarm) | messaging another swarm needs nothing more |
| `event` | **`swarm`**, **`repo`** | append-only, never loaded by a hook |

Indexes on every column a command filters by: `agent(swarm)`, `task(state)`, `task_repo(repo)`, `msg(dest, id)`,
`event(swarm, id)`, `workspace(agent)`, `lock(repo)`.

### Which swarm a command acts on

In order: `--swarm <name>` → `$SWARM` → the swarm of the agent row `$SWARM_NAME` names → the hc label `swarm=<name>`
on `$HC_TERMINAL_ID` (`join` sets it for every member, as it sets `swarm.comms` today) → the only live swarm → refuse,
listing the live swarms. Never the folder. Commands about a repo (`lock`, `task add`'s default repo, `ci`) take the
repo from the folder, or `--repo <path>`.

`swarm new <name> [--repo P]…` makes a swarm; `swarm join` with no swarm yet and a name like `<x>-comms` makes swarm
`<x>` for its communicator. `swarm swarms` lists them (live agents, communicator, repos).

## 3. The store: statements, not snapshots

A command is three parts, one `begin immediate` transaction:

1. **Reads**: keyed or filtered selects (`where swarm=?`, `where id=?`, `where state<>'done'`), using the indexes.
2. **A pure decision** on the rows read: `decide : Slice → Plan × α`, where `Slice` holds what the reads returned.
3. **A plan of statements**: the existing `Stmt` (`Db/Plan.lean`: `ins`, `upd`, `del`, keyed), plus a guarded update
   (`update … where <key> and <cond>`) whose `changes()` decides a race (a claim: `owner is null`).

No table is read to append to it: `Db.log` becomes an `ins` into `event`. `loadDb`, `storeDb` and `dbPlan` go once
every command is converted. WAL and `synchronous=normal` are already on (`Real.lean` `connect`); measure before
tuning anything else.

### How the proofs work afterwards (last phase)

The pieces exist: `Sql`/`SDb`/`Stmt.run`/`SqlExec` (`Assumptions.lean`) give each statement its meaning on a db, and
`swarm-tests`' `sqlite_spec` checks that meaning against real SQLite. The new shape:

- **Abstraction**: `abs : SDb → Db`, the db as the model sees it (the `Db` structure stays, as the model).
- **One lemma per statement kind**: `abs (run (ins r) d) = (abs d).insert r`, likewise `upd` = map at the key, `del` =
  filter, guarded `upd` = map where the guard holds, with `changes()` = whether it did. Proved once, used by everything.
- **Reads**: a filtered select returns `filter p (abs d)`; a decision that reads only its slice gets the same answer on
  any db with that slice (a frame lemma per command family).
- **Well-formedness** `WF : Db → Prop`: unique keys; a claimed task's owner is an agent row; one holder per lock per
  repo; `agent.swarm` names a swarm; `task_repo.repo` names a repo; one communicator per swarm; the existing board
  invariants (`Board.run_binv`, `one_owner_all`, `done_has_evidence`) restated over it.
- **Preservation**: for each command, `WF (abs d) → WF (abs (run (plan (decide (reads d))) d))`. With `WF empty` (the
  schema on a fresh db: no migration) that makes WF hold in every reachable db, by induction over committed
  transactions. `begin immediate` serialises transactions, so `Atomic`/`AllOrNothing` (Assumptions.lean) carry over.
- **Isolation of swarms** is then a WF consequence, not a separate rule: a command for swarm S writes only rows whose
  `swarm` is S or that belong to a repo/task, and states that in its plan's type.

### While the store changes

Proof files that stop compiling leave the build (their `import`s come out of `SwarmLean.lean`, their names out of
`comparator.json`, `Challenge.lean`/`Solution.lean` and `Audit.lean`'s expectations) and are listed in
`swarm/lean/SwarmLean/Proofs/LEGACY.md` with the commit that dropped them. `check.sh`'s gates stay (no `sorry`, no
new axiom, raw-git and kill checks); `swarm-tests` must stay green on every landing. The proofs phase brings each file
back in the new shape, or replaces it, and empties LEGACY.md.

## 4. watchd: one per machine

Its jobs, by what they are about:

- **per agent** (any swarm): reap dead, end landed, leases, context nudges and compaction, api-resume, hung stays;
- **per repo**: trial-merge conflicts among every agent with a worktree there, CI polling for the repo's base, PR
  polling, the worktree sweep (only worktrees a `workspace` row made);
- **per swarm**: auto-spawn (open startable tasks in the swarm's repos, within its `agent_min`/`agent_max`), typing
  messages into its communicator.

One `watchd` row in `meta` scope `''`; a second watchd is refused, `--takeover` as today. Its `--ci` and `--model`
become per-swarm meta knobs. The machine tick (pressure, oom_score_adj, orphans) is unchanged.

**Backup**: each hour watchd runs `VACUUM INTO '<state>/swarm/swarm.db.tmp'` and renames it over `swarm.db.bak`. One
copy.

## 5. The Herdr panels

`swarm state --json --view swarms` answers for the whole machine in one call (each swarm: communicator, staffing,
repos as objects with their base, latest CI run, lock count and the other live swarms on them, agents with their repo
and every repo they work in, tasks by state); the rail and `rw-swarms` call it once per machine (remote machines through
`hc exec`, as now) instead of once per space folder, and group by swarm. An agent row shows its repo. The rail
(direction B, board #91) lists per machine its swarms first, then its spaces with the terminals no swarm holds. "Open space"
becomes "focus the communicator's terminal". The side and swarm views take a swarm name, not a folder.

## 6. Build order (the board)

The running swarm uses the main checkout's binary (`~/.claude/skills/swarm` links there). Nobody builds, pulls or
edits in the main checkout while this runs, and tests run with `XDG_STATE_HOME`/`SWARM_DB` in a scratch dir.

1. **Foundation**: schema v2 at the machine path, `swarm`/`repo`/`swarm_repo`/`task_repo` tables, scoped `meta`,
   swarm resolution (§2), `swarm new`/`swarms`, `join` sets the label; `meta.space` and the "another repo" paths go.
   The whole-table store still runs underneath. Proofs that break move to LEGACY.md.
2. **Statement store** (after 1): reads + `decide` + plan in `Store`; the guarded update; `event` insert-only; indexes;
   the hooks converted first (hot path), measured before/after.
3. **Convert commands** (after 2), one task per family: tasks/queue; msgs/cursor; agents/join/spawn/end; locks and
   conflicts; watchd ticks. The last one removes `loadDb`/`storeDb`/`dbPlan`.
4. **Repos per task** (after 1): `task add --repo` (default: the folder's repo; repeatable; none allowed), bases from
   `repo`/`task_repo`, `spawn --task` makes one worktree per repo, landed checks per repo, locks per repo.
5. **One watchd per machine** (after 1): the three loops of §4, conflicts and CI per repo, backup.
6. **Herdr panels** (after 1): §5.
7. **Docs** (after 4, 5): SKILL.md, brief.md, DESIGN.md, settings.template.json.
8. **Proofs** (after 3-5): statement lemmas, WF and its preservation per family, isolation; LEGACY.md empty; the
   challenge gate back.

## 7. Open

- A task with no repo: staffed only by an explicit claim or `spawn --task`, never by auto-spawn. Revisit if research
  tasks pile up.
- Remote machines: each has its own db; a repo is a path on one machine. `swarm run --on` keeps working as today
  (its ledger is per machine already).
- `Lib/Cost.lean`'s `cmd` table and the compute ledger are separate dbs today; folding them in is a later task.
- A swarm's repos are set when it is made (`swarm new --repo`, or the folder's on a communicator's first `join`); no
  command adds or removes one later. Add `swarm new`-like `--repo` editing when a swarm first needs it.
- `swarm new <x>` without `--comms` leaves the swarm with no communicator, and a later `join` as `<x>-comms` does not
  set one (the swarm exists): the docs say `new … --comms <x>-comms`, and `watchd --comms` sets it.

Decided while writing the docs (#78):

- `lock`, `unlock` and `ci` take the folder's repo only; §2's `--repo <path>` is built for `task add` alone.
- `swarm board` lists every task on the machine (tasks belong to no swarm); auto-spawn staffs only those touching a
  repo of its swarm, and the Herdr swarm view groups them per swarm.
- `settings.template.json` already carried `SWARM={{GROUP}}` and no `SWARM_DB`; it needed no change. An agent's
  settings file and the `swarm` link on its PATH live beside the db (`<state>/swarm/agents/`, `<state>/swarm/bin/`).
- The communicator starts watchd as `swarm watchd --ci --comms $SWARM_NAME` (no `SWARM_COMMS`): in a second swarm on
  the machine that sets its knobs and is then refused, which is all it needs.

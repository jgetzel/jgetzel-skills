# Porting the swarm CLI to Lean

The swarm CLI (swarm/lua/swarm, LuaJIT) moves to Lean here, in this order: port until it is functional, move the
proofs over, delete the Lua. Board #97 laid the foundation and ported `task`, `board` and `rules` (tasks.lua,
bases.lua); #98-#101 port the rest in parallel on top of it. This file is what they build on.

## Progress

`./parity.sh` runs the Lua CLI's cli_*_spec.lua tests against swarm-lean and prints, per spec file, passed / failed /
not-ported. It is strict (SWARM_LEAN_STRICT=1): a command not ported fails, so a test counts as passed only when
every command it runs is ported. `./parity.sh --mixed` runs the same tests letting unported commands fall through to
the Lua CLI: every test must pass there, which checks each ported command against the Lua running the rest. Report a
port's progress as parity.sh's table; `./check.sh` runs both modes on both builds.

## Decisions

1. **Same database.** swarm-lean reads and writes the Lua CLI's SQLite db (`$SWARM_DB`, else
   `<git common dir>/swarm/swarm.db`), schema and migrations as db.lua's (`Real.lean`: `schema`, `columns`,
   `connect`). SQLite comes through `c/shim.c` (`@[extern]` in `Sqlite.lean`), linked to the repo flake's `sqlite`
   output (`nix build .#sqlite`, which the lakefile runs into `.lake/sqlite`; `$SWARM_SQLITE` overrides with a prefix
   holding lib/ and include/). The shim also gives `now`, the local `HH:MM` and `execvp`.
2. **Proof shape.** `Db` (`Db.lean`) holds every table as a list of rows plus the next id of each AUTOINCREMENT
   table. A command's effect is a pure `… → Db → Db × Except String α` (`Db/<module>.lean`), run by
   `Store.txn tables f`: BEGIN IMMEDIATE, load the listed tables, apply `f`, write back, COMMIT
   (`Real.lean`: `sqliteTxn`). The write-back diffs by primary key: deletes the rows gone, UPDATEs the changed ones
   (known columns only, so a column Lean does not know keeps its value), INSERTs the new. A table not loaded is empty
   in the `Db` and only gains the rows the step inserts (an event appended needs no load). `Atomic` stays the one
   store assumption; it now also covers "a step reads only the tables it lists". The slice's theorems are proved of
   the real steps (`Proofs.lean`).
3. **The world through interfaces** (`World.lean`, instances for `App` in `Real.lean`): `Store`, `Clock` (now, hhmm),
   `Env` (variables, stdout/stderr lines, stdin, cwd), `Fs` (read, list, write), `Proc` (output, exec, luaCli),
   `Git`. A command is generic in its monad `m` and asks for the classes it uses; early exit is
   `MonadExceptOf Exit m` (`die` writes `swarm: <msg>` and exits 1). No command calls IO. To add one (gh, hc, a
   process's spawn/wait/kill/alive): a class in `World.lean` (or its own file imported there), its `App` instance in
   `Real.lean`, and `[X m]` on the commands that use it.
4. **Layout.** One file per command group, `Cmd/<Group>.lean`, ending in `def group : Group m` (its parsers and its
   run); `Dispatch.groups` lists the groups, one line each (and one import). Pure steps per Lua module under `Db/`
   (`Db/Tasks.lean`, `Db/Agents.lean`, `Db/Msgs.lean`); world-facing helpers per Lua module under `Lib/`
   (`Lib/Machine.lean`, `Lib/Hook.lean`). Row types are all in `Db/Rows.lean` (the schema is fixed; a task adds a
   column there). A file belongs to the task porting its Lua module, so parallel tasks do not touch the same files:
   #98 Db/Msgs, Cmd/Msgs; #99 Lib/Hook, Cmd/Locks, Cmd/Hook; #100 Db/Agents, Lib/Machine, Cmd/Agents; #101 Cmd/Ci …
5. **main.** `Main.lean`: the first word picks a group (`Dispatch.find`); `Args.lean` parses the rest as argparse
   does (same errors, exit 2 with `Usage: swarm [-h] <command> ...` before `swarm: error: <msg>`; `-h` prints the
   help to stdout, exit 0). The `-h` texts are literals copied from the Lua (`./swarm <cmd> -h`), in
   `Cmd/<Group>Help.lean`. `Dispatch.runParsed` does main.lua's fence and the communicator's nudge, then the group.
   A word no group ports execs the Lua launcher with the same argv and environment (`$SWARM_LUA_CLI`, else the
   `swarm` next to `lua/swarm/main.lua` in a directory above the binary). With `SWARM_LEAN_STRICT=1` it fails
   instead: `swarm: not ported: <cmd>`, exit 1, and it appends `<cmd>` to `swarm-lean-not-ported` beside `$SWARM_DB`
   (how parity.sh tells a test that swallows the message).
6. **Parity.** `swarm/lua/test/cli.lua` runs `$SWARM_BIN` instead of the launcher when that is set, with
   `SWARM_LEAN_STRICT=1` unless the env sets it. It also gained `cli.DIR` (swarm/), which two specs now use for paths
   they derived from the launcher's.
7. **Ported here:** `task add/priority/after/claim/renew/show/done/block/unblock/release/edit/drop`, `board`, `rules`
   (all of tasks.lua's commands). #99: `lock`, `unlock`. bases.lua has no command; its helpers port with their first user (#100's endable,
   watchd's sweep). `--mixed` passes all 236 tests.
   #98: `post`, `read`, `wait`, `nudge` (msgs.lua, and agents.cmd_nudge) in Cmd/Msgs; msgs.lua's pure parts in
   Db/Msgs (`deliverStep` is deliver's pick as a step; Lib/Msgs's `deliver` formats it); agents.lua's hc helpers and
   cold rule in Lib/Agents. `wait --me` sets SWARM_NAME in `Dispatch.runParsed` (`Sys.setenv`), before the comms nudge
   reads it, as main.lua does.
   #100 so far: `join`, `leave`, `role`, `stay`, `limits`, `away`, `machine` (agents.lua's commands but who; machine.lua
   whole but cwds and claude_pid).
8. **Builds.** Stock Lean (`lake build`) and hpl (`hpl/`, every module `--all`). hpl compiles the whole program;
   the functions it refuses get Lean's C (listed below and by check.sh).
9. **Style.** One-sentence doc comments; no sorry/admit/axiom/native_decide; a Lua behaviour that looks wrong is
   ported as is and listed below.

## Beyond the above

- **One transaction per command.** The Lua runs some checks and writes outside its transaction (claim's dep check,
  `agents.touch`, the context check, the claim's event); here each command is one `Store.txn` (two for the fence),
  so it is at least as atomic. What the Lua wrote before a die inside its transaction still stays: the step returns
  that db with the error (claim's touch).
- **Read-only commands** (`board`, `task show`) take a snapshot (`Store.txn ts fun db => (db, db)`) and format it in
  the monad, since `HH:MM` is the world's.
- **Rows** are named as the columns (`lease_until`, `created_by`), every non-key column optional. `task.state` is
  `Status`; a state text Lean does not know fails the load. A cell of the wrong storage class is coerced as SQLite's
  affinity would (integral text in an int column reads as the integer).
- **Sys** (`Sys.lean`, its `App` instance in `RealSys.lean`, the C in `c/shim.c`): the process and file calls beyond
  `Env`/`Fs`/`Proc`, one class for every ported module (pid, alive, sleep, sub-second clock, `os.date`, hostname,
  environ, setenv, realpath, readlink, path kind, mtime, mkdir -p, hard link, remove, and `exec`: proc.exec with
  stdin, env unsets, merged stderr and a stdout file). A command that uses it asks for `[Sys m]`.
- **JSON** (`Lib/Json.lean`) is Lean's `Lean.Json`: compact as cjson, but object keys sorted where cjson follows the Lua
  table, so its readers parse it (the Herdr mod does); the same values and types otherwise.
- **Tests.** The Lua specs' asserts on ported pure functions are `#guard`s in `Tests/` (lean_lib `Tests`, built by
  `lake build`, so a failing one fails the build).
- **`try` in `App`** catches `Exit` (App's `ExceptT`), not `IO.Error`: an `App` instance method that must survive an
  IO error runs its body in `IO` (`(do try … catch … : IO _)`, as `RealSys.lean` does).
- **Locks** (#99): `covers` and `overlaps` are swarm/model's `Glob.lean` itself (the lakefiles build that one file as
  lean_lib `SwarmModelGlob`), over a path's bytes as Lua sees them; its proofs (`covers_iff`, `overlaps_iff`) are about
  the code that runs. Pure steps in `Db/Locks.lean`, `repo_rel` and the commands in `Cmd/Locks.lean`.
- **re.lua** is `Lib/Re.lean`, a backtracking matcher for the PCRE2 subset Python patterns use: literals, `.`,
  classes, `\w \s \d \b \A \z \Z ^ $`, groups (capturing, named, `(?:`, `(?=`, `(?!`, `(?ims)`), alternation,
  greedy and lazy quantifiers. Positions are characters. Not supported (a compile error): backreferences,
  lookbehind, the `x` flag. A possessive quantifier matches as greedy. Unicode classes are approximated (`shortcut:`
  in the file): non-ASCII is `\w` but for the common punctuation and symbol blocks, `\d` is ASCII, caseless folds
  ASCII.
- **difflib.lua, conflict.lua** (#99, #111): `Lib/Difflib.lean`, `Lib/Conflict.lean`: hunks, edits, clash, real_hunk,
  and the world parts (snapshot, onto, trial_merge, line_range, base_sha, `conflictTick`). The tick takes wt_map's
  agent→worktree list and bases.base_for as arguments (#100's), so watchd (#102) wires them. snapshot's temp
  index is made with `mktemp -d`, `cp -p` (which keeps the index's mtime to the nanosecond, where the Lua kept whole
  seconds: git rehashes no more) and `rm -rf` through `Proc`.
- **difflib.lua, conflict.lua** (#99): `Lib/Difflib.lean`, `Lib/Conflict.lean` (hunks, edits, clash, real_hunk).
- **ci, cost, run, state** (#101): `Cmd/Ci`, `Cmd/Cost`, `Cmd/Run`, `Cmd/State` (state, watch), their `-h` texts in
  `Cmd/OpsHelp`. ci.lua's watchd side (pr_ci, pr_watch, ci_poll, ci_check) is in `Lib/Ci` as pure steps on the db
  (`prCiApply`, `prWatchApply`, `ciPollApply`, `ciCheckStep`, `ciNewRedTask`) with gh's answers as arguments, and
  world wrappers (`prCi`, `prWatch`, `ciPoll`, `ciCheck`) for watchd; run.lua's watchd side (`remoteTick`,
  `cleanRemote`) and the job env are `Lib/Run`; cost.lua is `Lib/Cost` (its history db through `Sys.sqlAt`);
  bases.lua is `Lib/Bases`. Each watchd step takes its own transactions around the gh and git calls, where the Lua
  wrote as it went on one connection. `swarm run`'s command is split off before parsing in `Dispatch.run` (main.lua's
  split_run) and reaches the group as `argv`.
- **Proof statements.** `exactly_one_winner` now assumes each claim would succeed alone on the store as it was
  (the real claim also checks deps, a pending stop, the claimer's context and the lease text), where the slice
  assumed only "task i is open". The rest keep their shape over `Int` task ids and `Cmd`'s real arguments.

## Lua behaviours to revisit

Ported as they are:

- `task drop` drops a task in any state, done included.
- `tasks.stop_pending` compares the cursor with a NULL `stop_msg` (a Lua error); Lean reads NULL as 0.
- `task show` appends `, ctx Nk at claim` and ` -> Nk at done` to the priority (or base) line, not on a line of their
  own.
- `task claim` creates the agent's row (touch) before the context check, and keeps it when the claim is refused.
- The `task add` title limit counts bytes, not characters.
- `task release --after ""` stores deps as the empty string, not NULL.
- `board` prints `nil` for a `spawn_held` meta row whose value is NULL; `task unblock` says `only nil or the
  communicator` for a task with no owner.
- `unlock` logs an `unlock` event even when the agent held no such lock.
- `lock` replaces a dead or expired lock by `insert or replace`, which moves the row to the end of the table; Lean's
  write-back updates it in place, so when two locks cover one path `lock_holder` may name the other one (the Lua's
  order is SQLite's, unspecified, too).
- `hook.ctx_from` reads a transcript's last 300 KB as bytes; Lean drops the whole tail when the cut lands inside a
  UTF-8 character (`shortcut:` in Lib/Hook).
- `msgs.take` loops forever on a cursor row whose `last_msg_id` is NULL (its guarded UPDATE never matches); Lean reads
  it as 0 and moves it. Not ported as is: an endless loop.
- `swarm wait` on an agent row deleted under it fails in Lua (indexing nil); Lean exits 0, as superseded.
- `wait --poll` takes a decimal (`0.2`, `1`); Lua's `tonumber` also takes hex and exponents.
- `cost.key` strips `swarm run … -- ` only with a word between `run` and `--` (`swarm run -- make` keys as
  `swarm run --`).
- ci_check's "Later red" appends to the red task's body with SQL `||`, so a task with a NULL body keeps NULL.
- pr_ci matches a PR to a task with no owner by the head branch prefix `nil/` (Lua's `tostring(nil)`).
- `swarm watch` loads the event table whole each second (Store has no query; `shortcut:` in Cmd/State).
- `agents.session_active`'s `hc get` cache (`term_seen`) lives one command; Lean threads it as a value (`Seen`).

## hpl

The hpl build (`hpl/`) refuses these, all compiled with Lean's C instead (check.sh prints the current list):

| function | hpl's reason |
|---|---|
| `Agents.touch`, `Tasks.add`, `Tasks.drop._lam_0`, `Tasks.reopenF`, `Tasks.reopenFromF` | internal: a Option String is used where a Option Int is expected |
| `Machine.mem._redArg._lam_11` | internal: a Option String is used where a Option Float is expected |
| `outputIO` | internal: a Option String is used where a Option SwarmLean.ProcOut is expected |
| `Hook.ctxFrom._redArg._lam_3` | construction of a value of the builtin type `String` |
| `Cmd.Tasks.task._redArg`, `Hook.handoffNudge._redArg._lam_9` | partial application of a lambda which takes more than 16 arguments |
| `loadRows._redArg`, `storeRows._redArg` | partial application of a lambda which has a `void` parameter |
| `execIO'`, `execIO'._lam_1` (RealSys) | partial application of a lambda which has a `void` parameter |
| `Cmd.Run.run._redArg` and 33 of its lambdas, `Cmd.Ci.ci._redArg._lam_13`…`_lam_20` (6), `Ci.ciPoll…_lam_7`, `Ci.prWatch…_lam_5`, `Run.remoteTick…_lam_12`, `_lam_14` | partial application of a lambda which takes more than 16 arguments |
| `Ci.ciNewRedTask` | internal: a Option String is used where a Option Int is expected |
| `List.forIn'.loop…Cmd.Run.run…` (in Main) | partial application of a lambda which has a `void` parameter |
| `Cmd.Run.run…spec_26` (in Main) | variable has a type outside the subset |
| `Dispatch.runParsed…spec_3` (in Main) | variable has a type outside the subset |
| `Agents.hcTerminals…` (in Main, specialized for post) | internal: a Option String is used where a Option (List SwarmLean.Agents.Term) is expected |
| `Cmd.Msgs.post._redArg._lam_20`; `Cmd.Msgs.wait._redArg._lam_20`…`_lam_31` (8) | partial application of a lambda which takes more than 16 arguments |
| `List.forIn'.loop…` (in Main, post's loop), `repeatM…` (in Main, wait's loop) | partial application of a lambda which has a `void` parameter |
| `List.forIn'.loop…_lam_1` (post's loop), `Msgs.wakes…` (in Main, specialized for wait) | variable has a type outside the subset |

The "internal" ones look like hpl bugs (a structure update on a row with many optional fields).

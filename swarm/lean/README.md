# swarm-lean: the swarm CLI in Lean

The port of swarm/lua/swarm to Lean (PORT.md: the decisions, the layout, how a command group is added, what is
ported). `swarm-lean` takes the Lua CLI's command line and works on its SQLite db, so both run on one live swarm;
a command not ported yet runs the Lua CLI. Lean 4.35.0, no Lean dependencies; libsqlite3 from the repo flake.

| File | What it is |
|---|---|
| `SwarmLean/Db.lean`, `Db/Rows.lean` | the db: every table as rows, the next ids |
| `SwarmLean/Db/*.lean` | each Lua module's pure steps, `… → Db → Db × Except String α` |
| `SwarmLean/Store.lean`, `World.lean` | the interfaces (`Store`, `Clock`, `Env`, `Fs`, `Proc`, `Git`) and `Atomic` |
| `SwarmLean/Real.lean`, `Sqlite.lean`, `c/shim.c` | the real world: the SQLite store, IO |
| `SwarmLean/Args.lean`, `Cmd/*.lean`, `Dispatch.lean`, `Main.lean` | argparse's grammar, the command groups, main |
| `SwarmLean/Proofs.lean` | the slice's theorems about the real steps |
| `TestMain.lean`, `Tests/Cli/`, `Tests/Spec/` | `swarm-tests [pattern]`: the CLI's test suite (the Lua specs ported), parallel, per-test timeout |
| `Tests/*.lean` | the pure specs as `#guard`s, checked by `lake build` |
| `parity.sh` | the Lua cli specs against swarm-lean: passed / failed / not-ported per spec file |
| `test-claim.sh` | 50 `task claim 1` processes on one db; exactly one wins |
| `hpl/` | the same sources built with hpl (`../../../high-perf-lean`), every module `--all` |
| `check.sh` | build, no `sorry`/`axiom`, `Audit.lean`'s axioms, swarm-tests, parity.sh and test-claim.sh on both binaries |

Proved (no `sorry`, `admit`, `axiom` or `native_decide`), of the steps the CLI runs: the invariant (unique task ids
below the next id; a claimed task has an owner, an open one none) holds after any `task add`/`claim`/`release`/`board`
from the empty db (`run_inv`); no task has two owners (`one_owner`); two successful claims of a task have a
successful release between them (`claimed_once`); and, assuming `Atomic`, concurrent processes with no release get at
most one successful claim (`one_winner`), exactly one when each would have won alone (`exactly_one_winner`, what
`test-claim.sh` checks).

Not in CI: the repo has no workflow for swarm/, and one would need elan and the hpl checkout. Run `./check.sh`.

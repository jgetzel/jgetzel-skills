# swarm-lean: one slice of the swarm CLI in Lean

An experiment (board #96), not a port: `swarm-lean task add <title>`, `task claim <id>`, `task release <id>` and
`board`, run as `$SWARM_NAME` against its own store file (`$SWARM_LEAN_DB`, default `.claude/swarm-lean.json`).
The Lua CLI is untouched. Lean 4.35.0, no dependencies.

| File | What it is |
|---|---|
| `SwarmLean/Db.lean` | the db, the commands, `Cmd.step` (each command's whole effect, a pure function) and the JSON |
| `SwarmLean/Store.lean` | the `Store` interface, `Atomic` (the one assumption), the real store `fileTxn` |
| `SwarmLean/Proofs.lean` | `Inv` and the theorems, about `Cmd.step` itself |
| `Main.lean` | argument parsing and output; runs `Cmd.step` through `Store.txn` |
| `test-claim.sh` | 50 `task claim 1` processes started together; exactly one wins, the file parses after |
| `hpl/` | the same sources built with hpl (`../../../high-perf-lean`), every module `--all` |
| `check.sh` | build, no `sorry`/`axiom`, `Audit.lean`'s axiom list, `test-claim.sh` on both binaries |

The real store holds an exclusive `flock` (Lean's `IO.FS.Handle.lock`, no C shim) on `<db>.lock` across
read, apply and write, and writes a temp file renamed over the db.

Proved (no `sorry`, `admit`, `axiom` or `native_decide`): `Inv` (unique ids below `next`; a claimed task has an
owner, an open one none) holds of the empty db and after every `Cmd.step` (`run_inv`); no task has two owners after
any commands (`one_owner`); two `claimed` answers for one task have a successful release between them
(`claimed_once`); and, assuming `Atomic`, concurrent processes with no release get at most one `claimed`
(`one_winner`), exactly one when they all claim an open task (`exactly_one_winner`, what `test-claim.sh` checks).

Not in CI: the repo has no workflow for swarm/, and one would need elan and the hpl checkout. Run `./check.sh`.

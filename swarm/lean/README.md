# swarm-lean: the swarm CLI in Lean

The port of swarm/lua/swarm to Lean (PORT.md: the decisions, the layout, how a command group is added, what is
ported). `swarm-lean` takes the Lua CLI's command line and works on its SQLite db, so both run on one live swarm.
Every command is ported; with `SWARM_LEAN_STRICT=0` a command it does not know runs the Lua CLI (`../swarm-lua`),
otherwise it fails. Lean 4.35.0, no Lean dependencies; libsqlite3 from the repo flake.

## Install

The launcher `../swarm` runs `.lake/build/bin/swarm-lean` (or the nix link `.lake/nix`) when no source is newer than
it, else the Lua CLI with one stderr line naming `./build.sh`. That one command builds it either way:

- **elan + lake**: with `lake` on PATH ([elan](https://github.com/leanprover/elan) installs it and reads
  `lean-toolchain`), `lake build swarm-lean`, then a touch of the binary (lake keeps an up-to-date one's mtime).
- **nix**: otherwise, `nix build ../..#swarm-lean -o .lake/nix`, the repo flake's package (nixpkgs' Lean, which must
  match `lean-toolchain`). `nix run github:jgetzel/jgetzel-skills#swarm-lean -- board` also works, without the
  launcher's `SWARM_HERE`.

Rebuild after a pull that changes the sources. No prebuilt binaries are published: building from source is the only
route. The binary is about 11 MB: `c/shim.c` replaces `lean_initialize`, which Lean's `main` calls once any `Lean.*`
module is imported (here `Lean.Data.Json`) and which linked Lean's whole compiler library (120 MB before).

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
| `build.sh` | builds the binary the launcher runs (elan's lake, else nix) |
| `check.sh` | build, no `sorry`/`axiom`, `Audit.lean`'s axioms, swarm-tests, parity.sh and test-claim.sh on both binaries |

Proved (no `sorry`, `admit`, `axiom` or `native_decide`), of the steps the CLI runs: the invariant (unique task ids
below the next id; a claimed task has an owner, an open one none) holds after any `task add`/`claim`/`release`/`board`
from the empty db (`run_inv`); no task has two owners (`one_owner`); two successful claims of a task have a
successful release between them (`claimed_once`); and, assuming `Atomic`, concurrent processes with no release get at
most one successful claim (`one_winner`), exactly one when each would have won alone (`exactly_one_winner`, what
`test-claim.sh` checks).

CI: `.github/workflows/swarm-lean.yml` runs `./check.sh` on Linux and checks the launcher runs the binary. The hpl
build needs `../../../high-perf-lean`, outside this repo, so it runs locally only (`./check.sh` builds it when that
checkout has an hpl binary).

import Lake
open Lake DSL

/-- Compute claims: the ledger script, admission, and the `claim` tool (sw-compute-backfill.md §1a). Depends on nothing of swarm. -/
package claim

@[default_target]
lean_lib Claims

/-- The `#guard`s of the ledger's pure parts, checked when this builds. -/
@[default_target]
lean_lib ClaimTests where
  roots := #[`ClaimTests.Harness, `ClaimTests.Ledger, `ClaimTests.Script, `ClaimTests.Cli, `ClaimTests.Spec]

@[default_target]
lean_exe claim where
  root := `Main

/-- The script's cases and `claim`'s own, run by check.sh: `claim-tests [pattern]` (TestMain.lean). -/
@[default_target]
lean_exe «claim-tests» where
  root := `TestMain

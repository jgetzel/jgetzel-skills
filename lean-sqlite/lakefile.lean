import Lake
open Lake DSL System

/-- lean-sqlite: a clone of sqlite3 in Lean (stock build; hpl/ builds the same sources with hpl). -/
package «lean-sqlite» where
  moreLeancArgs := #["-O3"]

@[default_target]
lean_lib LSql

@[default_target]
lean_exe lsqlite3 where
  root := `Main

/-- The unit tests (#guard and the Tests module's cases). -/
lean_lib Tests


/-- Theorems about lean-sqlite (LSqlProofs.lean); not part of the executable. -/
lean_lib LSqlProofs

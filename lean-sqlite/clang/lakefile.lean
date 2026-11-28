import Lake
open Lake DSL System

/-- A control build: the lean-sqlite sources (`..`) compiled by stock Lean, but with the C toolchain the hpl build uses
(clang as high-perf-lean's `lake query hplcc` resolves it, `build.sh`), so stock-vs-hpl compares the compilers alone. -/
package «lean-sqlite-clang» where
  moreLeancArgs := #["-O3"]

lean_lib LSql where
  srcDir := ".."

@[default_target]
lean_exe lsqlite3 where
  srcDir := ".."
  root := `Main

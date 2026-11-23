import Lake
open Lake DSL System

/-- The lean-sqlite sources (`..`) built with hpl's C for every module, keeping Lean's data layout (`--all --no-unbox`):
hpl's other passes without its unboxed layouts, whose conversions at Lean-ABI boundaries (closures) cost more than they
save here (README.md, Benchmarks). -/
package «lean-sqlite-hpl-nounbox» where
  moreLinkArgs := #["-Wl,--gc-sections"]
  enableArtifactCache := true
  restoreAllArtifacts := true

require hpl from ".." / ".." / ".." / "high-perf-lean"

module_data hplO : FilePath

/-- Every module: all functions, Lean's layout. In the modules where a fused `List.range` loop under `--no-unbox` emits C
that does not compile (an undeclared `x_0`, hpl at f78b82312f), loop fusion is off. -/
def hplArgsOf : Lean.Name → Array String
  | `LSql.Compile | `LSql.Exec | `LSql.Check | `LSql.Shell | `Main => #["--all", "--no-unbox", "--disable", "fuse"]
  | _ => #["--all", "--no-unbox"]

module_facet hplArgs (mod : Module) : Option (Array String) := return .pure (some (hplArgsOf mod.name))

lean_lib LSql where
  srcDir := ".."
  nativeFacets := fun _ => #[(⟨Module.facetKind ++ `hplO, FamilyOut.fam_eq⟩ : ModuleFacet FilePath)]

@[default_target]
lean_exe lsqlite3 where
  srcDir := ".."
  root := `Main
  moreLinkArgs := #["@.lake/build/hpl-link.args"]
  nativeFacets := fun _ => #[(⟨Module.facetKind ++ `hplO, FamilyOut.fam_eq⟩ : ModuleFacet FilePath)]

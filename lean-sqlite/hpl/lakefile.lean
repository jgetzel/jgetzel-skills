import Lake
open Lake DSL System

/-- The lean-sqlite sources (`..`) built with hpl's C for every module (`--all`); the stock build is `..` itself. -/
package «lean-sqlite-hpl» where
  moreLinkArgs := #["-Wl,--gc-sections"]
  enableArtifactCache := true
  restoreAllArtifacts := true

require hpl from ".." / ".." / ".." / "high-perf-lean"

module_data hplO : FilePath

lean_lib LSql where
  srcDir := ".."
  nativeFacets := fun _ => #[(⟨Module.facetKind ++ `hplO, FamilyOut.fam_eq⟩ : ModuleFacet FilePath)]

@[default_target]
lean_exe lsqlite3 where
  srcDir := ".."
  root := `Main
  moreLinkArgs := #["@.lake/build/hpl-link.args"]
  nativeFacets := fun _ => #[(⟨Module.facetKind ++ `hplO, FamilyOut.fam_eq⟩ : ModuleFacet FilePath)]

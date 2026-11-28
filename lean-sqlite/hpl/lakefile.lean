import Lake
open Lake DSL System

/-- The lean-sqlite sources (`..`) built with hpl's C for every module (`--all`); the stock build is `..` itself. -/
package «lean-sqlite-hpl» where
  moreLinkArgs := #["-Wl,--gc-sections"]
  enableArtifactCache := true
  restoreAllArtifacts := true

/-- hpl's toolchain options (`-K cc= lto= leanrt= ld= relr= pie= cflags=`, `-K build=dev`), passed on to hpl. -/
def hplConfig : Lean.NameMap String :=
  [(`build, get_config? build), (`opt, get_config? opt), (`selfopt, get_config? selfopt), (`symbols, get_config? symbols),
   (`args, get_config? args), (`split, get_config? split), (`passcache, get_config? passcache), (`cc, get_config? cc), (`lto, get_config? lto),
   (`leanrt, get_config? leanrt), (`ld, get_config? ld), (`relr, get_config? relr), (`pie, get_config? pie), (`cflags, get_config? cflags)].foldl
    (fun m (k, v) => match v with | some v => m.insert k v | none => m) {}

require hpl from ".." / ".." / ".." / "high-perf-lean" with hplConfig

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

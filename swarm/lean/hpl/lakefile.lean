import Lake
open Lake DSL System

/-- The swarm-lean sources (`..`) built with hpl's C for every module (`--all`); the stock build is `..` itself. -/
package «swarm-lean-hpl»

/-- The hpl binary: $HPL, else the one built in ../high-perf-lean beside this repo. -/
def hplBin : IO FilePath := do
  return (← IO.getEnv "HPL").getD (← IO.FS.realPath (__dir__ / "../../../../high-perf-lean/.lake/build/bin/hpl")).toString

/-- Object file for a module: hpl's C for every function hpl accepts and Lean's C for the ones it refuses (listed in
`.lake/build/ir/hpl/<Module>.refused`), as in high-perf-lean's tests/lake/lakefile.lean with a binary path for `require`. -/
module_facet hplO (mod : Module) : FilePath := do
  let exe ← hplBin
  let oleanJob ← mod.leanArts.fetch
  let cFile := mod.pkg.irDir / "hpl" / (mod.name.toString ++ ".c")
  let refused := mod.pkg.irDir / "hpl" / (mod.name.toString ++ ".refused")
  let cJob ← oleanJob.mapM fun _ => do
    addTrace (← computeTrace (TextFilePath.mk mod.leanFile)); addTrace (← computeTrace exe)
    buildFileUnlessUpToDate' cFile do
      IO.FS.createDirAll cFile.parent.get!
      proc { cmd := exe.toString, env := #[("LEAN_PATH", some (← getWorkspace).augmentedLeanPath.toString)]
             args := #[mod.leanFile.toString, "-o", cFile.toString, "--setup", mod.setupFile.toString, "--all",
               "--refused", refused.toString] }
    return cFile
  buildLeanO (mod.irDir / "hpl" / (mod.name.toString ++ ".o")) cJob mod.weakLeancArgs
    (mod.leancArgs ++ #["-DLEAN_EXPORTING"])

lean_lib SwarmLean where
  srcDir := ".."
  roots := #[`SwarmLean.Db, `SwarmLean.Store]
  nativeFacets := fun _ => #[(⟨Module.facetKind ++ `hplO, FamilyOut.fam_eq⟩ : ModuleFacet FilePath)]

@[default_target]
lean_exe «swarm-lean» where
  srcDir := ".."
  root := `Main
  nativeFacets := fun _ => #[(⟨Module.facetKind ++ `hplO, FamilyOut.fam_eq⟩ : ModuleFacet FilePath)]

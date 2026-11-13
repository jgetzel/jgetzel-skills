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

/-- The sqlite library and header, as in ../lakefile.lean: $SWARM_SQLITE, else the flake output there. -/
def sqlitePrefix : IO FilePath := do
  if let some p ← IO.getEnv "SWARM_SQLITE" then if p ≠ "" then return p
  let out := __dir__ / ".." / ".lake" / "sqlite"
  unless ← out.pathExists do
    IO.FS.createDirAll (__dir__ / ".." / ".lake")
    let r ← IO.Process.output { cmd := "nix", args := #["build", "-o", out.toString, s!"{__dir__}/../../..#sqlite"] }
    if r.exitCode ≠ 0 then throw <| IO.userError s!"nix build of the flake's sqlite failed: {r.stderr}"
  return out

/-- Link flags for sqlite: its lib dir on the search path and the rpath. -/
def sqliteLink : IO (Array String) := do
  let lib := (← sqlitePrefix) / "lib"
  return #[s!"-L{lib}", "-lsqlite3", s!"-Wl,-rpath,{← IO.FS.realPath lib}"]

/-- The C shim, as in ../lakefile.lean (plain C: hpl compiles Lean, not C). -/
target shim.o pkg : FilePath := do
  let src ← inputTextFile (pkg.dir / ".." / "c" / "shim.c")
  let inc := (← sqlitePrefix) / "include"
  buildO (pkg.buildDir / "c" / "shim.o") src #["-I", inc.toString] #["-fPIC", "-O2"] (← getLeanc)

extern_lib libswarmshim pkg := do
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "swarmshim") #[← shim.o.fetch]

/-- locks.lua's glob, as in ../lakefile.lean. -/
lean_lib SwarmModelGlob where
  srcDir := "../../model"
  roots := #[`SwarmModel.Glob, `SwarmModel.Model, `SwarmModel.PrWatch, `SwarmModel.Decide]
  nativeFacets := fun _ => #[(⟨Module.facetKind ++ `hplO, FamilyOut.fam_eq⟩ : ModuleFacet FilePath)]

lean_lib SwarmLean where
  srcDir := ".."
  roots := #[`SwarmLean]
  nativeFacets := fun _ => #[(⟨Module.facetKind ++ `hplO, FamilyOut.fam_eq⟩ : ModuleFacet FilePath)]

@[default_target]
lean_exe «swarm-lean» where
  srcDir := ".."
  root := `Main
  moreLinkArgs := run_io sqliteLink
  nativeFacets := fun _ => #[(⟨Module.facetKind ++ `hplO, FamilyOut.fam_eq⟩ : ModuleFacet FilePath)]

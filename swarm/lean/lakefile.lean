import Lake
open Lake DSL System

package «swarm-lean»

/-- The sqlite library and header: $SWARM_SQLITE (a prefix with lib/ and include/), else the repo flake's `sqlite`
output, built into .lake/sqlite (a GC root). -/
def sqlitePrefix : IO FilePath := do
  if let some p ← IO.getEnv "SWARM_SQLITE" then if p ≠ "" then return p
  let out := __dir__ / ".lake" / "sqlite"
  unless ← out.pathExists do
    IO.FS.createDirAll (__dir__ / ".lake")
    let r ← IO.Process.output { cmd := "nix", args := #["build", "-o", out.toString, s!"{__dir__}/../..#sqlite"] }
    if r.exitCode ≠ 0 then throw <| IO.userError s!"nix build of the flake's sqlite failed: {r.stderr}"
  return out

/-- Link flags for sqlite: its lib dir on the search path and the rpath. -/
def sqliteLink : IO (Array String) := do
  let lib := (← sqlitePrefix) / "lib"
  return #[s!"-L{lib}", "-lsqlite3", s!"-Wl,-rpath,{← IO.FS.realPath lib}"]

@[default_target]
lean_lib SwarmLean

/-- The Lua specs' asserts on the ported pure functions, as `#guard`s checked when this builds. -/
@[default_target]
lean_lib Tests

/-- locks.lua's glob and watchd's keeps, lifted and proved in ../model: built from those files (and what Decide imports), not
copied. -/
lean_lib SwarmModelGlob where
  srcDir := "../model"
  roots := #[`SwarmModel.Glob, `SwarmModel.Model, `SwarmModel.PrWatch, `SwarmModel.Decide]

@[default_target]
lean_exe «swarm-lean» where
  root := `Main
  moreLinkArgs := run_io sqliteLink

/-- The C shim (c/shim.c), compiled against Lean's and sqlite's headers. -/
target shim.o pkg : FilePath := do
  let src ← inputTextFile (pkg.dir / "c" / "shim.c")
  let inc := (← sqlitePrefix) / "include"
  buildO (pkg.buildDir / "c" / "shim.o") src #["-I", inc.toString] #["-fPIC", "-O2"] (← getLeanc)

extern_lib libswarmshim pkg := do
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "swarmshim") #[← shim.o.fetch]

import SwarmModel.Lua.Run

/-! `lake env lean --run SwarmModel/LuaRun.lean <file.lua>...`: each chunk's results under the Lean interpreter, as
`../lua/test/luasem.lua` writes LuaJIT's (`luajit ../lua/test/luasem.lua <file.lua>...`), with every swarm module
loadable. -/

open Swarm.Lua

def main (args : List String) : IO Unit := do
  let srcs ← loadSources "../lua/swarm"
  for f in args do
    let b ← IO.FS.readBinFile f
    let text := String.fromUTF8! b
    -- the modules it requires: require "swarm.x"
    let mods := (text.splitOn "require \"swarm.").tail.map fun s => "swarm." ++ (s.takeWhile (· != '"')).toString
    IO.println s!"{f}: {runCase (srcsOf srcs) mods (bytesOf b)}"

import LuaLean.Gen

/-! `lua-lean cases <n> <seed> <file>`: `n` random chunks with the Lean interpreter's results (`LuaLean/Gen.lean`),
for `luajit test/luasem.lua --cases <file>` run from lua-lean/: some require and dofile the modules in test/mods. -/

def main (args : List String) : IO UInt32 := do
  let [n, seed, file] := args | do IO.eprintln "usage: Cases.lean <n> <seed> <file>"; return 1
  let srcs ← Lua.loadSources "test/mods"
  Lua.Gen.writeCases (return (← if ← Lua.Gen.chance 12 then Lua.Gen.files else Lua.Gen.chunk, [])) (Lua.srcsOf srcs)
    n.toNat! seed.toNat! file
  return 0

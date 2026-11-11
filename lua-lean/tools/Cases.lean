import LuaLean.Gen

/-! `lua-lean cases <n> <seed> <file>`: `n` random chunks with the Lean interpreter's results (`LuaLean/Gen.lean`),
for `luajit test/luasem.lua --cases <file>`. -/

def main (args : List String) : IO UInt32 := do
  let [n, seed, file] := args | do IO.eprintln "usage: Cases.lean <n> <seed> <file>"; return 1
  Lua.Gen.writeCases (return (← Lua.Gen.chunk, [])) (fun _ => none) n.toNat! seed.toNat! file
  return 0

import LuaLean.Gen

/-! Random Lua chunks with the Lean interpreter's results, for ../lua/test/luasem_spec.lua to run under LuaJIT and
compare: lua-lean's (`LuaLean/Gen.lean`), and calls of the codebase's own pure functions (util.lua, locks.lua,
difflib.lua) on random arguments. `lake env lean --run SwarmModel/LuaCases.lean <n> <seed> <file>` (replay.sh). -/

open Lua Lua.Gen

-- ---------- the codebase's functions ----------

def utilCase : G String := do
  let s := q (← str " ab/\n,.'-_" 10)
  let s2 := q (← str " ab/,." 4)
  let call ← pick [
    s!"util.split({s})", s!"util.split({s}, {← pick ["\",\"", "\" \"", "\"/\"", "\"ab\""]})", s!"util.strip({s})",
    s!"util.splitlines({s})", s!"util.startswith({s}, {s2})", s!"util.endswith({s}, {s2})", s!"util.basename({s})",
    s!"util.dirname({s})", s!"util.join({s}, {s2}, {← q <$> str "/ab" 3})", s!"util.shquote({s})",
    s!"util.shjoin(\{{s}, {s2}})", s!"util.d({← pick ["0", "7", "1e15", "-3", "2^40"]})",
    s!"util.dur({← q <$> pick ["90s", "30m", "2h", "5", "0m", "12h"]})"]
  return s!"local util = require \"swarm.util\"\nreturn {call}"

def lockPat : G String := do
  if ← chance 2 then str "aabb//.*?[]!^-\\" 8 else
  let mut r := ""
  for _ in [0:← rnd 5] do
    r := r ++ (← pick ["*", "?", "[ab]", "[!a]", "[a-b]", "a", "b", "/", "."])
  return r

def locksCase : G String := do
  let p ← lockPat
  let p2 ← lockPat
  let x ← str "ab/.*?[]!\\" 8
  return s!"local locks = require \"swarm.locks\"
return locks.covers({q x}, {q p}), locks.overlaps({q p}, {q p2}), locks.tokens({q p}), locks.covers({q p2}, {q p})"

def difflibCase : G String := do
  let arr : G String := do
    let xs ← (List.range (← rnd 7)).mapM fun _ => do return q (← pick ["a", "b", "c", "d"])
    return "{" ++ commas xs ++ "}"
  return s!"local difflib = require \"swarm.difflib\"
local m = difflib.SequenceMatcher({← arr}, {← arr})
return m:get_opcodes(), m:get_matching_blocks()"

def swarmChunk : G (String × List String) := do
  match ← rnd 10 with
  | 8 => if ← chance 2 then return (← utilCase, ["swarm.util"]) else return (← difflibCase, ["swarm.difflib"])
  | 9 => return (← locksCase, ["swarm.locks"])
  | _ => return (← Gen.chunk, [])

def main (args : List String) : IO UInt32 := do
  let [n, seed, file] := args | do IO.eprintln "usage: LuaCases.lean <n> <seed> <file>"; return 1
  let srcs ← loadSources "../lua/swarm"
  writeCases swarmChunk (srcsOf srcs) n.toNat! seed.toNat! file "../lua/?.lua"
  return 0

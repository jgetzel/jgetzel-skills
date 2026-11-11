import LuaLean.Parse

/-! `test/out.txt`'s chunks, one a line: LuaJIT's syntax beyond Lua 5.1 that the subset leaves out (DESIGN.md, "The
subset"). LuaJIT loads each (check.sh) and the parser must refuse each. -/

open Lua

def main (args : List String) : IO UInt32 := do
  let [file] := args | do IO.eprintln "usage: Refused.lean <file>"; return 2
  let mut bad : UInt32 := 0
  for l in ← IO.FS.lines file do
    if let .ok _ := parseChunk (bytesOf l.toUTF8) "c" then IO.eprintln s!"parsed, but out of the subset: {l}"; bad := 1
  return bad

import LuaLean.Print

/-! `lua-lean print <file.lua>` prints the parsed file back as Lua, fully
parenthesised, for comparing its LuaJIT bytecode with the source's (`lua-lean parsecheck`). -/

open Lua

def main (args : List String) : IO UInt32 := do
  let [file] := args | do IO.eprintln "usage: Print.lean <file.lua>"; return 1
  match parseChunk (bytesOf (← IO.FS.readBinFile file)) file with
  | .error e => IO.eprintln e; return 1
  | .ok b => IO.print (Print.block b); return 0

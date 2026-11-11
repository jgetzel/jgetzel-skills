import SwarmModel.Lua.Show

/-! `lake env lean --run SwarmModel/LuaDump.lean (<module> <file.lua>)...` prints each parsed file as a Lean definition
`<module>Src : Block`: a syntax tree proofs can be about (board #39). -/

open Swarm.Lua Swarm.Lua.Show

def dump (name file : String) : IO Bool := do
  let bytes ← IO.FS.readBinFile file
  match parseChunk (bytesOf bytes) with
  | .error e => IO.eprintln s!"{file}: {e}"; return false
  | .ok b =>
    IO.println s!"/-- swarm/lua/swarm/{(System.FilePath.mk file).fileName.getD file}, parsed -/\ndef {name}Src : Block :={block b}\n-- checksum {name} {checksum bytes}\n"
    return true

def main (args : List String) : IO UInt32 := do
  let rec go : List String → IO Bool
    | [] => pure true
    | name :: file :: rest => do let a ← dump name file; let b ← go rest; pure (a && b)
    | _ => do IO.eprintln "usage: LuaDump.lean (<module> <file.lua>)..."; pure false
  return if args.isEmpty || !(← go args) then 1 else 0

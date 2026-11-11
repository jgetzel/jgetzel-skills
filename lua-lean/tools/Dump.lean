import LuaLean.Show

/-! `lua-lean dump (<Name> <file.lua>)...` prints each parsed file as a Lean definition
`<Name>Src : Block`: a syntax tree proofs can be about. -/

open Lua Lua.Show

def dump (name file : String) : IO Bool := do
  let bytes ← IO.FS.readBinFile file
  match parseChunk (bytesOf bytes) ((System.FilePath.mk file).fileName.getD file) with
  | .error e => IO.eprintln s!"{file}: {e}"; return false
  | .ok b =>
    IO.println s!"/-- {(System.FilePath.mk file).fileName.getD file}, parsed -/\ndef {name}Src : Block :={block b}\n-- checksum {name} {checksum bytes}\n"
    return true

def main (args : List String) : IO UInt32 := do
  let rec go : List String → IO Bool
    | [] => pure true
    | name :: file :: rest => do let a ← dump name file; let b ← go rest; pure (a && b)
    | _ => do IO.eprintln "usage: Dump.lean (<Name> <file.lua>)..."; pure false
  return if args.isEmpty || !(← go args) then 1 else 0

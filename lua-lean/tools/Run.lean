import LuaLean.Run

/-! `lua-lean run [--lib <prefix>=<dir>]... <file.lua>...`: each chunk's results under the Lean interpreter, as
`test/luasem.lua` writes LuaJIT's (`luajit test/luasem.lua <file.lua>...`). With `--lib p=dir`, `require "p.x"` loads
dir/x.lua; a module the chunk requires is loaded first, its effects opaque handles. -/

open Lua

def main (args : List String) : IO UInt32 := do
  let rec split : List String → List (String × String) × List String
    | "--lib" :: l :: rest => let (ls, fs) := split rest
      match l.splitOn "=" with | [p, d] => ((p, d) :: ls, fs) | _ => (ls, l :: fs)
    | f :: rest => let (ls, fs) := split rest; (ls, f :: fs)
    | [] => ([], [])
  let (libs, files) := split args
  if files.isEmpty then IO.eprintln "usage: Run.lean [--lib <prefix>=<dir>]... <file.lua>..."; return 1
  let srcs ← libs.flatMapM fun (p, d) => loadSources d p
  for f in files do
    let b ← IO.FS.readBinFile f
    let text := String.fromUTF8! b
    let mods := libs.flatMap fun (p, _) =>
      (text.splitOn s!"require \"{p}.").tail.map fun s => s!"{p}." ++ (s.takeWhile (· != '"')).toString
    IO.println s!"{f}: {runCase (srcsOf srcs) mods (bytesOf b)}"
  return 0

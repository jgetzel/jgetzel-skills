import SwarmLean.Dispatch
import SwarmLean.Real
open SwarmLean

/-- A command not ported yet: the Lua CLI with the same argv and environment, or under SWARM_LEAN_STRICT=1 a failure. -/
def fallThrough (args : List String) : IO UInt32 := do
  let w := args.headD ""
  if (← IO.getEnv "SWARM_LEAN_STRICT") == some "1" then
    IO.eprintln s!"swarm: not ported: {w}"
    -- for parity.sh: a test that swallows the message still leaves this in its fixture, beside its db
    if let some db ← IO.getEnv "SWARM_DB" then
      if let some dir := (db : System.FilePath).parent then
        try
          let h ← IO.FS.Handle.mk (dir / "swarm-lean-not-ported") .append
          h.putStrLn w
        catch _ => pure ()
    return 1
  match ← luaCliIO with
  | none => IO.eprintln s!"swarm: not ported: {w}, and the Lua CLI is not found (set SWARM_LUA_CLI)"; return 127
  | some lua =>
    let why ← execIO (lua :: args)
    IO.eprintln s!"swarm: can't run the Lua CLI {lua}: {why}"
    return 127

def main (args : List String) : IO UInt32 := do
  match args with
  | w :: rest =>
    match Dispatch.find (m := App) w with
    | none => fallThrough args
    | some (g, spec) =>
      let ctx : Ctx := { conn := ← IO.mkRef none }
      try
        match ← (Dispatch.run g spec rest).run ctx with
        | .ok code => pure code
        | .error e => pure e.code
      catch e =>
        IO.eprintln s!"swarm: {e}"
        pure 1
  | [] => fallThrough args

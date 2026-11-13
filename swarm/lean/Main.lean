import SwarmLean.Dispatch
import SwarmLean.Real
import SwarmLean.RealSys
open SwarmLean

/-- No known command word: `-h` prints the commands; anything else is argparse's usage error (exit 2). -/
def noCommand (args : List String) : IO UInt32 := do
  match args.head? with
  | some "-h" | some "--help" => IO.println (Dispatch.help (m := App)); return 0
  | some w => IO.eprintln s!"{Dispatch.USAGE}\nswarm: error: unknown command '{w}'"; return 2
  | none => IO.eprintln s!"{Dispatch.USAGE}\nswarm: error: a command is required"; return 2

def main (args : List String) : IO UInt32 := do
  match args with
  | w :: rest =>
    match Dispatch.find (m := App) w with
    | none => noCommand args
    | some (g, spec) =>
      let ctx : Ctx := { conn := ← IO.mkRef none }
      try
        match ← (Dispatch.run g spec rest).run ctx with
        | .ok code => pure code
        | .error e => pure e.code
      catch e =>
        IO.eprintln s!"swarm: {e}"
        pure 1
  | [] => noCommand args

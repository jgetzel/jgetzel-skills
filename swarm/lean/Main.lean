import SwarmLean.Dispatch
import SwarmLean.Real
import SwarmLean.RealSys
open SwarmLean

set_option maxHeartbeats 800000 in
/-- No known command word: `-h` prints the commands; anything else is argparse's usage error (exit 2). -/
def noCommand (args : List String) : IO UInt32 := do
  match args.head? with
  | some "-h" | some "--help" => IO.println (Dispatch.help (m := App)); return 0
  | some w => IO.eprintln s!"{Dispatch.USAGE}\nswarm: error: unknown command '{w}'"; return 2
  | none => IO.eprintln s!"{Dispatch.USAGE}\nswarm: error: a command is required"; return 2

/-- `args` without the global `--swarm <name>` (`--swarm=<name>`) before any `--`, and the name it gave. -/
def swarmOpt : List String → List String × Option String
  | [] => ([], none)
  | "--" :: rest => ("--" :: rest, none)
  | "--swarm" :: s :: rest => ((swarmOpt rest).1, some s)
  | a :: rest =>
    if a.startsWith "--swarm=" then ((swarmOpt rest).1, some (a.drop 8).toString)
    else let (r, s) := swarmOpt rest; (a :: r, s)

def main (args0 : List String) : IO UInt32 := do
  let (args, sw) := swarmOpt args0
  if let some s := sw then setenvIO "SWARM" s
  match args with
  | w :: rest =>
    match Dispatch.find (m := App) w with
    | none => noCommand args
    | some (g, spec) =>
      let ctx : Ctx := (← Ctx.new)
      try
        match ← (Dispatch.run g spec rest).run ctx with
        | .ok code => pure code
        | .error e => pure e.code
      catch e =>
        IO.eprintln s!"swarm: {e}"
        pure 1
  | [] => noCommand args

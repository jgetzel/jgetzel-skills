import SwarmLean.Store
open SwarmLean

/-- The command a command line asks for, as `agent`. -/
def parse (agent : Option String) : List String → Except String Cmd
  | ["board"] => pure .board
  | "task" :: "add" :: title@(_ :: _) => pure (.add (" ".intercalate title))
  | ["task", verb, id] => do
    let some i := id.toNat? | throw s!"not a task id: {id}"
    let some a := agent | throw "SWARM_NAME is not set"
    match verb with
    | "claim" => pure (.claim i a)
    | "release" => pure (.release i a)
    | _ => throw s!"unknown: task {verb}"
  | _ => throw "usage: swarm-lean task add <title> | task claim <id> | task release <id> | board"

/-- An answer's text, and whether it is a success. -/
def render : Result → String × Bool
  | .added i => (s!"added #{i}", true)
  | .claimed => ("claimed", true)
  | .held o => (s!"held by {o.getD "?"}", false)
  | .notOpen => ("not open", false)
  | .released => ("released", true)
  | .notYours => ("not claimed by you", false)
  | .noSuch => ("no such task", false)
  | .board ts => ("\n".intercalate (ts.map fun t =>
      s!"#{t.id} {match t.status with | .open => "open" | .claimed => "claimed" | .done => "done"} {t.owner.getD "-"}  {t.title}"), true)

def main (args : List String) : IO UInt32 := do
  let path : System.FilePath := (← IO.getEnv "SWARM_LEAN_DB").getD ".claude/swarm-lean.json"
  match parse ((← IO.getEnv "SWARM_NAME").filter (· ≠ "")) args with
  | .error e => IO.eprintln e; pure 2
  | .ok c =>
    let (out, ok) := render (← ReaderT.run (exec c) path)
    (if ok then IO.println out else IO.eprintln out)
    pure (if ok then 0 else 1)

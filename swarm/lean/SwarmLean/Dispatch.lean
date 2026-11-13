import SwarmLean.Cmd.Tasks
import SwarmLean.Sys
import SwarmLean.Cmd.Msgs
import SwarmLean.Cmd.Locks
import SwarmLean.Cmd.Agents
import SwarmLean.Cmd.Cost
import SwarmLean.Cmd.Ci
import SwarmLean.Cmd.Run
import SwarmLean.Cmd.State
import SwarmLean.Cmd.Hook
import SwarmLean.Lib.Hook
import SwarmLean.Lib.Agents

/-! The ported command groups and main.lua's dispatch around them: the fence and the communicator's nudge. -/

namespace SwarmLean.Dispatch
open Args

variable {m : Type → Type} [Monad m] [MonadExceptOf Exit m] [Store m] [Clock m] [Env m] [Fs m] [Proc m] [Git m] [Sys m]

/-- Every ported group: a new group is one line here (and its import above). -/
def groups : List (Group m) := [
  Cmd.Tasks.group,
  Cmd.Msgs.group,
  Cmd.Locks.group,
  Cmd.Agents.group,
  Cmd.Cost.group,
  Cmd.Ci.group,
  Cmd.Run.group,
  Cmd.State.group,
  Cmd.Hook.group
]

/-- main.lua's root usage, printed before a parse error. -/
def USAGE : String := "Usage: swarm [-h] <command> ..."

/-- The commands main.lua fences: their writes are refused to a terminal the agent is not bound to. -/
def FENCED : List String := ["post", "read", "task", "lock", "unlock", "leave", "stay"]

/-- The commands that stand in for the communicator's post-tool hook (hook.comms_nudge). -/
def NUDGED : List String := ["read", "wait", "board", "who"]

/-- The group and parser that port command word `w`, if any. -/
def find (w : String) : Option (Group m × Spec) :=
  (groups (m := m)).findSome? fun g => (g.specs.lookup w).map (g, ·)

/-- Runs a ported command line as main.lua's main does after parsing: fence, nudge, then the group. -/
def runParsed (g : Group m) (a : Parsed) : m UInt32 := do
  if a.cmd == "wait" then if let some n := a.str "me" then Sys.setenv "SWARM_NAME" n
  if let some name ← env "SWARM_NAME" then
    if FENCED.contains a.cmd && a.act != "show" then
      let here ← env "HC_TERMINAL_ID"
      if let some f ← Store.txn [.agent, .event] fun db => (db, Agents.fence db name here) then
        die (← Agents.fenceText name f)
  if NUDGED.contains a.cmd then Hook.commsNudge (a.cmd == "wait")
  g.run a

/-- Parses and runs `w :: rest` with group `g`'s parser `spec`: exit 2 on a parse error, 0 after `-h`. -/
def run (g : Group m) (spec : Spec) (rest : List String) : m UInt32 := do
  -- `run`'s command is split off before parsing (main.lua's split_run): the parse gets its options only
  let (rest, argv) := if spec.name == "run" then Cmd.Run.split rest else (rest, [])
  match parse spec "cmd" "" rest with
  | .error (.error msg) => Env.err s!"{USAGE}\nswarm: error: {msg}"; return 2
  | .error (.help h) => Env.out h; return 0
  | .ok a => runParsed g (if spec.name == "run" then ("argv", .ss argv) :: a else a)

end SwarmLean.Dispatch

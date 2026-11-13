import SwarmLean.Cmd.Tasks
import SwarmLean.Lib.Hook

/-! The ported command groups and main.lua's dispatch around them: the fence and the communicator's nudge. -/

namespace SwarmLean.Dispatch
open Args

variable {m : Type → Type} [Monad m] [MonadExceptOf Exit m] [Store m] [Clock m] [Env m] [Fs m] [Proc m]

/-- Every ported group: a new group is one line here (and its import above). -/
def groups : List (Group m) := [
  Cmd.Tasks.group
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
  if let some name ← env "SWARM_NAME" then
    if FENCED.contains a.cmd && a.act != "show" then
      let here ← env "HC_TERMINAL_ID"
      match ← Store.txn [.agent, .event] fun db => (db, Agents.fence db name here) with
      | some (.ended t why) =>
        let tail := match why with | some w => if w != "" then s!" ({w})" else "" | none => ""
        die s!"{name} was ended at {← Clock.hhmm (t.getD 0)}{tail}; `swarm join` to return."
      | some (.bound hc here) =>
        die s!"{name} is bound to {hc}; this terminal is {here.getD "outside Herdr"}. `swarm join --takeover` moves it here."
      | none => pure ()
  if NUDGED.contains a.cmd then Hook.commsNudge (a.cmd == "wait")
  g.run a

/-- Parses and runs `w :: rest` with group `g`'s parser `spec`: exit 2 on a parse error, 0 after `-h`. -/
def run (g : Group m) (spec : Spec) (rest : List String) : m UInt32 := do
  match parse spec "cmd" "" rest with
  | .error (.error msg) => Env.err s!"{USAGE}\nswarm: error: {msg}"; return 2
  | .error (.help h) => Env.out h; return 0
  | .ok a => runParsed g a

end SwarmLean.Dispatch

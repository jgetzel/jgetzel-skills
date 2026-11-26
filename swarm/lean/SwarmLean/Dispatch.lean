import SwarmLean.Cmd.Tasks
import SwarmLean.Sys
import SwarmLean.Cmd.Msgs
import SwarmLean.Cmd.Locks
import SwarmLean.Cmd.Agents
import SwarmLean.Cmd.Cost
import SwarmLean.Cmd.Ci
import SwarmLean.Cmd.Pr
import SwarmLean.Cmd.Run
import SwarmLean.Cmd.Compute
import SwarmLean.Cmd.State
import SwarmLean.Cmd.Hook
import SwarmLean.Cmd.Watchd
import SwarmLean.Lib.Hook
import SwarmLean.Lib.Agents
import SwarmLean.Lib.Sock

/-! The ported command groups and main.lua's dispatch around them: the fence and the communicator's nudge. -/

namespace SwarmLean.Dispatch
open Args

variable {m : Type → Type} [Monad m] [MonadExceptOf Exit m] [Store m] [Clock m] [Env m] [Fs m] [Proc m] [Git m] [Sys m] [Guard m] [Scoped m]

/-- Every ported group: a new group is one line here (and its import above). -/
def groups : List (Group m) := [
  Cmd.Tasks.group,
  Cmd.Msgs.group,
  Cmd.Locks.group,
  Cmd.Agents.group,
  Cmd.Cost.group,
  Cmd.Ci.group,
  Cmd.Pr.group,
  Cmd.Run.group,
  Cmd.Compute.group,
  Cmd.State.group,
  Cmd.Hook.group,
  Cmd.Watchd.group
]

/-- main.lua's root usage, printed before a parse error. -/
def USAGE : String := "Usage: swarm [-h] [--swarm <name>] <command> ..."

/-- `swarm -h`'s sections: a title, then each command with its line. A command of `groups` left out of every section
goes to the last line, so the list stays whole. -/
def SECTIONS : List (String × List (String × String)) := [
  ("Work", [
    ("board", "the tasks, the agents and the swarm's agent max; run it first"),
    ("queue", "Ready in order: looking for work, take its first startable entry"),
    ("task", "claim, renew, show, done, land, release, block, add, edit, … (`swarm task -h`)"),
    ("run", "run a build or test on claimed cores and memory, here or on another machine"),
    ("cost", "what a command took here before"),
    ("machine", "this machine's memory and load: read it before a build or test"),
    ("ci", "a commit's CI as watchd polled it: exit 0 green, 1 red, 2 pending"),
    ("lock", "reserve paths git can't see (a glob or dir/) for every swarm in the repo"),
    ("unlock", "free a lock")]),
  ("Talk and wait", [
    ("read", "your unread messages"),
    ("post", "message an agent, @all, @<swarm> or a task ('#N')"),
    ("who", "the swarm's agents"),
    ("role", "say what you do (implementer, reviewer, lander, …)"),
    ("stay", "declare what you wait for, so watchd won't end you"),
    ("endable", "exit 0 if nothing keeps you from being ended; --why lists what does"),
    ("compact", "compact your own context"),
    ("spawn", "start a peer agent in a new tab")]),
  ("Communicator and user", [
    ("join", "bind a name to this terminal; a communicator's join makes its swarm"),
    ("wait", "block until a message comes (the communicator's waiter; agents' Stop hook runs it)"),
    ("nudge", "type one fixed line into an agent's terminal: read your messages and continue"),
    ("end", "end an agent's terminal once it is idle with its work landed"),
    ("leave", "unbind an agent"),
    ("rules", "the rules every spawn's first message carries"),
    ("limits", "auto-spawn number, agent max and context thresholds"),
    ("away", "mark the user away, or back"),
    ("new", "make a swarm"),
    ("swarms", "the machine's swarms"),
    ("pr", "squash-merge PRs once their checks are green"),
    ("worktrees", "remove the worktrees whose work is in a base")]),
  ("Machine and panels", [
    ("watchd", "the machine's daemon: staffing, messages, compaction, CI, sweeps"),
    ("compute", "the core and memory claims on each machine; caps and reservations"),
    ("job", "record a job that ran elsewhere"),
    ("state", "a JSON snapshot for the Herdr panels"),
    ("events", "the machine's events as JSON"),
    ("watch", "the events as they come"),
    ("hook", "Claude Code's hooks for swarm agents")])]

/-- `swarm -h`: the usage, every command by section with its line, then where commands act. -/
def help : String :=
  let names := (groups (m := m)).flatMap (·.specs.map (·.1))
  let listed := SECTIONS.flatMap (·.2.map (·.1))
  let line (c : String × String) := "  " ++ c.1 ++ "".pushn ' ' (12 - c.1.length) ++ c.2
  let secs := SECTIONS.map fun (t, cs) =>
    t ++ ":\n" ++ "\n".intercalate ((cs.filter (names.contains ·.1)).map line)
  let rest := names.filter (!listed.contains ·)
  s!"{USAGE}\n\n" ++ "\n\n".intercalate secs ++
  (if rest.isEmpty then "" else s!"\n\nOther: {", ".intercalate rest}") ++ "\n\n" ++
  "`swarm <command> -h` (or `swarm help <command>`) explains a command and lists its subcommands.\n\n" ++
  "One db per machine: $XDG_STATE_HOME/swarm/swarm.db (else ~/.local/state; $SWARM_DB for tests). A command acts on one\n" ++
  "swarm (a group of agents): --swarm <name>, else $SWARM, else the swarm of $SWARM_NAME's agent, else the terminal's hc\n" ++
  "label swarm=<name>, else the only live swarm; never the folder. Tasks, locks, CI and worktrees belong to repos:\n" ++
  "`lock`, `ci` and `task add` take the folder's. `swarm swarms` lists the swarms, `swarm new` makes one."

/-- The commands main.lua fences: their writes are refused to a terminal the agent is not bound to. -/
def FENCED : List String := ["post", "read", "task", "lock", "unlock", "leave", "stay", "queue", "compact"]

/-- The commands that stand in for the communicator's post-tool hook (hook.comms_nudge). -/
def NUDGED : List String := ["read", "wait", "board", "who"]

/-- The group and parser that port command word `w`, if any. -/
def find (w : String) : Option (Group m × Spec) :=
  (groups (m := m)).findSome? fun g => (g.specs.lookup w).map (g, ·)

/-- Runs a ported command line as main.lua's main does after parsing: fence, the inbox socket's record, nudge, then the
group. -/
def runParsed (g : Group m) (a : Parsed) : m UInt32 := do
  if a.cmd == "wait" then if let some n := a.str "me" then Sys.setenv "SWARM_NAME" n
  if let some name ← env "SWARM_NAME" then
    if FENCED.contains a.cmd && a.act != "show" then
      let here ← env "HC_TERMINAL_ID"
      if let some f ← Store.view (Sels.fence name) fun db => Agents.fence db name here then
        die (← Agents.fenceText name f)
    Sock.record name  -- the session's inbox socket, where watchd posts (board #215)
  if NUDGED.contains a.cmd then Hook.commsNudge (a.cmd == "wait")
  g.run a

/-- Parses and runs `w :: rest` with group `g`'s parser `spec`: exit 2 on a parse error, 0 after `-h`. -/
def run (g : Group m) (spec : Spec) (rest : List String) : m UInt32 := do
  -- `run`'s command is split off before parsing (main.lua's split_run): the parse gets its options only
  let (rest, argv) := if spec.name == "run" then Cmd.Run.split rest else if spec.name == "job" then Cmd.Run.splitJob rest
    else if spec.name == "compute" then (rest.takeWhile (· != "--"), (rest.dropWhile (· != "--")).drop 1) else (rest, [])
  -- `board --json`: the Board view's snapshot, as `state --json --view board` prints it (board #200)
  let (g, spec, rest) := if spec.name == "board" && rest.contains "--json" && !rest.contains "-h" && !rest.contains "--help" then
      (Cmd.State.group, Cmd.State.stateSpec, ["--json", "--view", "board"]) else (g, spec, rest)
  match parse spec "cmd" "" rest with
  | .error (.error msg) => Env.err s!"{USAGE}\nswarm: error: {msg}"; return 2
  | .error (.help h) => Env.out h; return 0
  | .ok a => runParsed g (if spec.name == "run" || spec.name == "job" || spec.name == "compute" then ("argv", .ss argv) :: a else a)

end SwarmLean.Dispatch

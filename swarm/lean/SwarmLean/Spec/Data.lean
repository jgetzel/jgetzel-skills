import SwarmLean.Db
import SwarmLean.Lib.Re
import SwarmModel.Glob

/-! The spec layer's data (board #216): the types the code's steps take and return and the few functions of the code
that a hypothesis or an invariant of the challenged theorems reads (`Challenge.lean`), moved here from `Db/` and `Lib/`
under their own names so that the challenge can import them with no implementation. -/

namespace SwarmLean.Agents

/-- The user's name (agents.HUMAN). -/
def HUMAN : String := "human"

/-- Why this terminal may not write as `name` (agents.fence), before the time is formatted. -/
inductive Fence
  /-- the row ended at `t`; `why` is the data of its last reap, leave or end event -/
  | ended (t : Option Int) (why : Option String)
  /-- the row is bound to terminal `hc`; this one is `here` -/
  | bound (hc : String) (here : Option String)

/-- A row's binding as bind reads it before its transaction: its terminal and when it ended. -/
abbrev Binding := Option (Option String × Option Int)

/-- A question waiting in the away digest: a blocked task and since when. -/
structure Question where
  id : Nat
  title : Option String
  owner : Option String
  question : Option String
  since : Option Int

/-- What happened while the user was away (agents.digest). -/
structure Digest where
  since : Option Int
  back : Int
  note : Option String
  questions : List Question
  done : List Task
  merged : List Task
  ci : Option Ci
  /-- each ended agent: name, when, why -/
  ended : List (String × Option Int × Option String)
  hung : List String

/-- A terminal as `hc ls --json` lists it. -/
structure Term where
  state : Option String
  address : Option String
  name : Option String := none
  cwd : Option String := none
  status : Option String := none

end SwarmLean.Agents

namespace SwarmLean.Msgs

/-- Where `name`'s cursor stands: the last id it read. -/
def cursorOf (db : Db) (name : String) : Int := ((db.cursor name).bind (·.last_msg_id)).getD 0

end SwarmLean.Msgs

namespace SwarmLean.Tasks
open Agents

/-- What a task command knows of the world, read before it runs. -/
structure Ctx where
  /-- the agent ($SWARM_NAME) -/
  me : String
  now : Int
  /-- $HC_TERMINAL_ID, none when unset or empty -/
  here : Option String := none
  /-- $SWARM_COMMS, none when unset or empty -/
  comms : Option String := none
  /-- the working directory -/
  cwd : Option String := none
  /-- `task claim --force`: the communicator claims a Backlog task, or a Ready one assigned to another -/
  force : Bool := false
  /-- `task done` of a landing task: its evidence names a commit on the task's base (checked with git first) -/
  onBase : Bool := false

/-- What `task add` was given. -/
structure AddArgs where
  title : String
  body : String := ""
  deps : List Int := []
  model : Option String := none
  effort : Option String := none
  base : Option String := none
  priority : Option Priority := none
  /-- `--label`: its labels, comma-separated as given -/
  labels : Option String := none

/-- What a successful claim prints: the lease's end and the body. -/
structure Claimed where
  «until» : Int
  body : Option String

/-- What `task unland` reopened: the former owner, and the task's new priority. -/
structure Unlanded where
  owner : Option String
  priority : Priority

/-- What `task done` says after: a red task goes to Backlog until a green run; a landing task closed by its lander,
with its former owner; else the context line's parts. -/
inductive DoneOut
  | red
  | done (k : Int) (stay : Option String) (poolSize : Nat)
  | landed (owner : Option String)

/-- What `task edit` was given. -/
structure EditArgs where
  title : Option String := none
  body : Option String := none
  /-- `--body-file`: its path and text, none when it could not be read -/
  bodyFile : Option (String × Option String) := none
  append : Option String := none
  model : Option String := none
  effort : Option String := none
  /-- `task label`: the new labels (`labelsText`; "" clears them) -/
  labels : Option String := none
  urgent : Bool := false

end SwarmLean.Tasks

namespace SwarmLean.Spawn

/-- Why a reservation failed: a die (`swarm: …`), the user's max (`refused`) or a lost race (`lost`), both printed as
they are. -/
inductive Refusal
  | die (msg : String)
  | refused (msg : String)
  | lost (msg : String)

end SwarmLean.Spawn

namespace SwarmLean.Queue

/-- Where `queue add` puts its ids. -/
inductive Place
  | back
  | front
  | before (id : Int)
  | after (id : Int)

end SwarmLean.Queue

namespace SwarmLean.Locks

/-- A Lua string's bytes as the `Char`s below 256 that Glob.lean reads. -/
def bytes (s : String) : List Char := s.toUTF8.toList.map fun b => Char.ofNat b.toNat

/-- Whether lock pattern `pat` covers `path` (locks.covers). -/
def covers (path pat : String) : Bool := Swarm.Glob.covers true (bytes path) (bytes pat)

/-- Whether some path is covered by both lock patterns (locks.overlaps). -/
def overlaps (p q : String) : Bool := Swarm.Glob.overlaps true (bytes p) (bytes q)

end SwarmLean.Locks

namespace SwarmLean.Machine

/-- One process as `ps` lists it (a row of machine.parse_ps). -/
structure Ps where
  pid : Int
  ppid : Int
  rss_kb : Int
  age : Int
  cpu_s : Int
  args : String
  argv : List String
  comm : String
  deriving Repr, BEq, Inhabited

end SwarmLean.Machine

namespace SwarmLean.Lifecycle

/-- Fate's reads of one agent, each made only when asked (watchd.reads(…).f(n)). -/
structure Reads (m : Type → Type) where
  /-- it owns a claimed or blocked task -/
  claims : Bool
  /-- it holds a lock -/
  locks : Bool
  /-- its background job: a Bash-tool shell under its claude process -/
  job : m (Option Machine.Ps)
  /-- a worktree of its with work not on its bases, and those refs -/
  unlanded : m (Option (String × List String))
  /-- how many tasks it would be offered (`Reuse.candidates`) -/
  pool : Nat
  /-- the reuse threshold (`Reuse.reuseBelow`); 0 is off -/
  below : Nat
  /-- process `pid` lives -/
  alive : Int → m Bool
  /-- it was offered every task it would be and has read what would wake it -/
  passedOver : Bool

/-- What a fate run heard: each check made, in order, with whether it held; the unlanded worktree and its refs (once
that check was made); the job's process (once that one was). -/
structure Heard where
  checks : List (String × Bool) := []
  held : Option (String × List String) := none
  proc : Option Machine.Ps := none

end SwarmLean.Lifecycle

namespace SwarmLean.Run

/-- Under each machine's home: `<repo>/<worktree>/{src,jobs/<id>}`. -/
def RUN_DIR : String := ".cache/swarm-run"

/-- A path `RUN_DIR/<repo>/<worktree>`, the whole string. -/
def RUN_DIR_RE : Re.Pat := .lit ("\\A" ++ Re.escape RUN_DIR ++ "/[\\w.-]+/[\\w.-]+\\z")

/-- A job's copy, `RUN_DIR/<repo>/<worktree>`, with no `..` that would climb out of it. -/
def runDirOk (dir : String) : Bool :=
  RUN_DIR_RE.test dir && !(dir.splitOn "/").contains ".."

end SwarmLean.Run

namespace SwarmLean.Watchd

/-- A worktree untouched this long (s) may be swept. -/
def SWEEP_IDLE : Int := 1800

end SwarmLean.Watchd

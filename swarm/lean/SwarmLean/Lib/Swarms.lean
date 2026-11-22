import SwarmLean.Sys
import SwarmLean.Db.Schema
import Std.Data.HashMap
import Std.Data.HashSet

/-! The machine's swarms (sw-global §2): the one db, the `swarm`, `repo`, `swarm_repo` and `task_repo` tables, read
and written outside the store's transactions (they belong to no swarm's scope). -/

namespace SwarmLean.Swarms
open Sqlite (Val)

variable {m : Type → Type} [Monad m] [Env m] [Sys m]

/-- The machine's db: $SWARM_DB (tests), else swarm/swarm.db in $XDG_STATE_HOME, else in ~/.local/state. -/
def dbPath : m String := do
  if let some p ← env "SWARM_DB" then return p
  let st ← match ← env "XDG_STATE_HOME" with
    | some x => pure x
    | none => pure (((← env "HOME").getD "") ++ "/.local/state")
  return st ++ "/swarm/swarm.db"

/-- A swarm on the machine: its communicator, when it was made and ended, its repos and live agents. -/
structure Row where
  name : String
  comms : Option String := none
  created : Option Int := none
  ended : Option Int := none
  repos : List String := []
  live : List String := []

/-- A cell as text. -/
def txt : Option Val → Option String
  | some (.text s) => some s
  | _ => none

/-- A cell as an integer. -/
def int : Option Val → Option Int
  | some (.int i) => some i
  | _ => none

/-- Every swarm, by name. -/
def list : m (List Row) := do
  let rs ← Sys.sqlAt (← dbPath) schema [("select name, comms, created, ended from swarm order by name", []),
    ("select swarm, repo from swarm_repo order by swarm, repo", []),
    ("select swarm, name from agent where swarm is not null and ended is null order by name", [])]
  let of (i : Nat) (s : String) : List String :=
    ((rs.getD i #[]).toList.filter fun r => txt r[0]? == some s).filterMap (txt ·[1]?)
  return (rs.headD #[]).toList.filterMap fun r => (txt r[0]?).map fun name =>
    { name, comms := txt r[1]?, created := int r[2]?, ended := int r[3]?, repos := of 1 name, live := of 2 name }

/-- Makes swarm `s` with communicator `comms` and repos (path, base) at time `t`; false when it exists. -/
def create (sn : SwarmName) (comms : Option String) (repos : List (String × Option String)) (t : Int) : m Bool := do
  let s := sn.val
  let txt (o : Option String) : Val := match o with | some x => .text x | none => .null
  let rs ← Sys.sqlAt (← dbPath) schema ([("select 1 from swarm where name=?", [.text s]),
      ("insert or ignore into swarm(name, comms, created) values(?, ?, ?)", [.text s, txt comms, .int t])] ++
    repos.flatMap fun (p, b) => [("insert or ignore into repo(path, base) values(?, ?)", [.text p, txt b]),
      ("insert or ignore into swarm_repo(swarm, repo) values(?, ?)", [.text s, .text p])])
  return (rs.headD #[]).isEmpty

/-- The swarm agent `n`'s row is in, if any. -/
def ofAgent (n : String) : m (Option String) := do
  let rs ← Sys.sqlAt (← dbPath) schema [("select swarm from agent where name=? and swarm is not null", [.text n])]
  return ((rs.headD #[])[0]?).bind (txt ·[0]?)

/-- The swarm a communicator named `<x>-comms` (a digit suffix allowed: `<x>-comms2`) makes: `x`. -/
def ofComms (n : String) : Option String :=
  let c := (n.toList.reverse.dropWhile Char.isDigit).reverse
  let s := String.ofList c
  if s.endsWith "-comms" && s.length > 6 then some (String.ofList (c.take (c.length - 6))) else none

/-- A cell as text or null. -/
def ov (o : Option String) : Val := match o with | some x => .text x | none => .null

/-- The repo row of `p` (a main worktree), made when first seen with `base` (`.claude/swarm.json`'s). -/
def seeRepo (p : String) (base : Option String) : m Unit := do
  discard <| Sys.sqlAt (← dbPath) schema [("insert or ignore into repo(path, base) values(?, ?)", [.text p, ov base])]

/-- The base recorded for repo `p`, if any. -/
def repoBase (p : String) : m (Option String) := do
  let rs ← Sys.sqlAt (← dbPath) schema [("select base from repo where path=?", [.text p])] true
  return ((rs.headD #[])[0]?).bind (txt ·[0]?)

/-- Task `id` touches each repo of `repos` (path, its base there; none: the repo's), each repo row made when first
seen with its base. -/
def addTaskRepos (id : Int) (repos : List (String × Option String × Option String)) : m Unit := do
  if repos.isEmpty then return
  discard <| Sys.sqlAt (← dbPath) schema (repos.flatMap fun (p, own, rb) =>
    [("insert or ignore into repo(path, base) values(?, ?)", [.text p, ov rb]),
     ("insert or ignore into task_repo(task, repo, base) values(?, ?, ?)", [.int id, .text p, ov own])])

/-- The repos task `id` touches, each with its own base there (none: the repo's), in the order they were added. -/
def taskRepos (id : Int) : m (List (String × Option String)) := do
  let rs ← Sys.sqlAt (← dbPath) schema [("select repo, base from task_repo where task=? order by rowid", [.int id])] true
  return (rs.headD #[]).toList.filterMap fun r => (txt r[0]?).map (·, txt r[1]?)

/-- The ids of the tasks that touch repo `p` (its `task_repo` rows): what the repo's CI passes act on (board #136). -/
def tasksOf (p : String) : m (List Int) := do
  let rs ← Sys.sqlAt (← dbPath) schema [("select task from task_repo where repo=? order by task", [.text p])] true
  return (rs.headD #[]).toList.filterMap (int ·[0]?)

/-- Every task's id and state text, in id order: one two-column select, for counts and deps' states without the
rows. -/
def taskStates : m (List (Int × String)) := do
  let rs ← Sys.sqlAt (← dbPath) schema [("select id, state from task order by id", [])] true
  return (rs.headD #[]).toList.filterMap fun r => match int r[0]?, txt r[1]? with
    | some i, some s => some (i, s)
    | _, _ => none

/-- The repos of swarm `s`: those its auto-spawn staffs from. -/
def reposOf (s : String) : m (List String) := do
  let rs ← Sys.sqlAt (← dbPath) schema [("select repo from swarm_repo where swarm=? order by repo", [.text s])] true
  return (rs.headD #[]).toList.filterMap (txt ·[0]?)

/-- The tasks that touch a repo of swarm `s`: the ones its auto-spawn may staff. -/
def staffable (s : String) : m (List Int) := do
  let rs ← Sys.sqlAt (← dbPath) schema [("select distinct tr.task from task_repo tr join swarm_repo sr on sr.repo = tr.repo " ++
    "where sr.swarm=? order by tr.task", [.text s])] true
  return (rs.headD #[]).toList.filterMap (int ·[0]?)

/-- Task `k` is swarm `s`'s: one of its repos is the swarm's, a member owns or added it, or it has no repo and no swarm's
agent owns or added it (a task before `task_repo`, or the human's: every swarm's board shows it). -/
def mine (repos : List String) (members everyone : Std.HashSet String) (taskRepos : List String) (owner by_ : Option String) :
    Bool :=
  taskRepos.any repos.contains || owner.any members.contains || by_.any members.contains ||
    (taskRepos.isEmpty && !owner.any everyone.contains && !by_.any everyone.contains)

/-- The ids of swarm `s`'s tasks (`mine`): what its panel's board and Next up list (sw-global §5). -/
def mineIds (s : String) : m (Std.HashSet Int) := do
  let rs ← Sys.sqlAt (← dbPath) schema [
    ("select id, owner, created_by from task", []),
    ("select task, repo from task_repo", []),
    ("select name, swarm from agent where swarm is not null", []),
    ("select repo from swarm_repo where swarm=?", [.text s])] true
  let rows (i : Nat) : List (Array Val) := (rs.getD i #[]).toList
  let taskRepos : Std.HashMap Int (List String) := (rows 1).foldl (init := {}) fun h r =>
    match int r[0]?, txt r[1]? with
    | some k, some rp => h.insert k (rp :: h.getD k [])
    | _, _ => h
  let everyone : Std.HashSet String := (rows 2).foldl (init := {}) fun h r =>
    match txt r[0]? with
    | some a => h.insert a
    | none => h
  let members : Std.HashSet String := (rows 2).foldl (init := {}) fun h r =>
    match txt r[0]?, txt r[1]? with
    | some a, some w => if w == s then h.insert a else h
    | _, _ => h
  let repos := (rows 3).filterMap (txt ·[0]?)
  return (rows 0).foldl (init := {}) fun h r =>
    match int r[0]? with
    | some k =>
      if mine repos members everyone (taskRepos.getD k []) (py (txt r[1]?)) (py (txt r[2]?)) then h.insert k
      else h
    | none => h

end SwarmLean.Swarms

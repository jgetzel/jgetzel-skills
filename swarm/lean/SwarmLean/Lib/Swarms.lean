import SwarmLean.Sys
import SwarmLean.Db.Schema

/-! The machine's swarms (sw-global §2): the one db, the `swarm`, `repo` and `swarm_repo` tables, read and written
outside the store's transactions (they belong to no swarm's scope). -/

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
def create (s : String) (comms : Option String) (repos : List (String × Option String)) (t : Int) : m Bool := do
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

end SwarmLean.Swarms

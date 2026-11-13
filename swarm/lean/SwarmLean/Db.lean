import SwarmLean.Db.Rows

namespace SwarmLean

/-- The whole database: every table of the schema as its rows (in rowid or key order, as loaded), and the id the next
insert into each AUTOINCREMENT table gets. A command loads only the tables it reads (`Table`); the others stay empty
here and only gain the rows it inserts. -/
structure Db where
  agents : List Agent := []
  msgs : List Msg := []
  cursors : List Cursor := []
  tasks : List Task := []
  locks : List Lock := []
  conflicts : List Conflict := []
  pairkeys : List Pairkey := []
  metas : List Meta := []
  events : List Event := []
  workspaces : List Workspace := []
  cis : List Ci := []
  taskNext : Nat := 1
  msgNext : Nat := 1
  eventNext : Nat := 1
  deriving DecidableEq, Repr, Inhabited

/-- A table of the schema. -/
inductive Table
  | agent | msg | cursor | task | lock | conflict | pairkey | «meta» | event | workspace | ci
  deriving DecidableEq, Repr

/-- The task with id `i`. -/
def Db.find (db : Db) (i : Int) : Option Task := db.tasks.find? (fun t => (t.id : Int) == i)

/-- `db` with `f` applied to the task with id `i`. -/
def Db.set (db : Db) (i : Int) (f : Task → Task) : Db :=
  { db with tasks := db.tasks.map fun t => if (t.id : Int) = i then f t else t }

/-- The agent row named `n`. -/
def Db.agent (db : Db) (n : String) : Option Agent := db.agents.find? (·.name == n)

/-- `db` with `f` applied to the agent row named `n`. -/
def Db.setAgent (db : Db) (n : String) (f : Agent → Agent) : Db :=
  { db with agents := db.agents.map fun a => if a.name = n then f a else a }

/-- The meta row with key `k`. -/
def Db.getMeta (db : Db) (k : String) : Option Meta := db.metas.find? (·.k == k)

/-- `db` with meta `k` set to `v` (insert or replace). -/
def Db.setMeta (db : Db) (k : String) (v : Option String) : Db :=
  if db.metas.any (·.k == k) then { db with metas := db.metas.map fun m => if m.k = k then { m with v } else m }
  else { db with metas := db.metas ++ [{ k, v }] }

/-- `db` with an event appended to the log (db.log). -/
def Db.log (db : Db) (ts : Int) (agent : Option String) (kind : String) (path data : Option String) : Db :=
  { db with events := db.events ++ [{ id := db.eventNext, ts, agent, kind, path, data }], eventNext := db.eventNext + 1 }

/-- The cursor row of agent `n`. -/
def Db.cursor (db : Db) (n : String) : Option Cursor := db.cursors.find? (·.agent == n)

end SwarmLean

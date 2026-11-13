import Lean.Data.Json
open Lean (ToJson FromJson)

namespace SwarmLean

/-- Where a task is in its life. -/
inductive Status
  | «open» | claimed | done
  deriving DecidableEq, Repr, ToJson, FromJson

/-- One board task. -/
structure Task where
  id : Nat
  title : String
  status : Status
  owner : Option String
  deriving DecidableEq, Repr, ToJson, FromJson

/-- The whole store: the tasks and the id the next `add` hands out. -/
structure Db where
  tasks : List Task := []
  next : Nat := 1
  deriving DecidableEq, Repr, ToJson, FromJson

/-- A command of the slice; `claim` and `release` carry the agent ($SWARM_NAME). -/
inductive Cmd
  | add (title : String)
  | claim (id : Nat) (agent : String)
  | release (id : Nat) (agent : String)
  | board
  deriving DecidableEq, Repr

/-- What a command answers. -/
inductive Result
  | added (id : Nat)
  | claimed
  | held (owner : Option String)
  | notOpen
  | released
  | notYours
  | noSuch
  | board (tasks : List Task)
  deriving DecidableEq, Repr

/-- The task with id `i`. -/
def Db.find (db : Db) (i : Nat) : Option Task := db.tasks.find? (·.id == i)

/-- `db` with `f` applied to the task with id `i`. -/
def Db.set (db : Db) (i : Nat) (f : Task → Task) : Db :=
  { db with tasks := db.tasks.map fun t => if t.id = i then f t else t }

/-- A command's whole effect on the store, and its answer. -/
def Cmd.step : Cmd → Db → Db × Result
  | .add title, db => ({ tasks := db.tasks ++ [⟨db.next, title, .open, none⟩], next := db.next + 1 }, .added db.next)
  | .claim i a, db => match db.find i with
    | none => (db, .noSuch)
    | some t => match t.status with
      | .open => (db.set i ({ · with status := .claimed, owner := some a }), .claimed)
      | .claimed => (db, .held t.owner)
      | .done => (db, .notOpen)
  | .release i a, db => match db.find i with
    | none => (db, .noSuch)
    | some t =>
      if t.status = .claimed ∧ t.owner = some a then (db.set i ({ · with status := .open, owner := none }), .released)
      else (db, .notYours)
  | .board, db => (db, .board db.tasks)

/-- The store file's text for `db`. -/
def Db.encode (db : Db) : String := (Lean.toJson db).compress

/-- The db a store file holds. -/
def Db.decode (s : String) : Except String Db := Lean.Json.parse s >>= Lean.fromJson?

end SwarmLean

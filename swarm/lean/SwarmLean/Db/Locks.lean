import SwarmLean.Db.Tasks
import SwarmModel.Glob

/-! locks.lua's pure parts: covers and overlaps (swarm/model's Glob.lean, proved there), the lock holder, an agent's
task line, and lock/unlock as steps. -/

namespace SwarmLean.Locks
open Agents

/-- A Lua string's bytes as the `Char`s below 256 that Glob.lean reads. -/
def bytes (s : String) : List Char := s.toUTF8.toList.map fun b => Char.ofNat b.toNat

/-- Whether lock pattern `pat` covers `path` (locks.covers). -/
def covers (path pat : String) : Bool := Swarm.Glob.covers true (bytes path) (bytes pat)

/-- Whether some path is covered by both lock patterns (locks.overlaps). -/
def overlaps (p q : String) : Bool := Swarm.Glob.overlaps true (bytes p) (bytes q)

/-- The live, unexpired locks of agents other than `me`, in load order (lock_holder's and cmd_lock's join). -/
def others (db : Db) (me : String) (now : Int) : List Lock :=
  db.locks.filter fun l => match l.agent with
    | some a => a != me && l.lease_until.any (· > now) && db.agents.any fun g => g.name == a && g.ended.isNone
    | none => false

/-- Another live agent's lock that covers `path` (locks.lock_holder). -/
def lockHolder (db : Db) (me path : String) (now : Int) : Option Lock :=
  (others db me now).find? fun l => covers path l.path

/-- `task #N: title` of the first task `name` holds, else `no claimed task` (locks.task_of). -/
def taskOf (db : Db) (name : String) : String :=
  let held := db.tasks.filter fun t => t.owner == some name && (t.state = .claimed || t.state = .blocked)
  match held.mergeSort (·.id ≤ ·.id) with
  | t :: _ => s!"task #{d t.id}: {t.title.getD ""}"
  | [] => "no claimed task"

/-- `swarm lock` on the repo-relative `path`: refused for an ended agent (a lock `swarm join` would bring back unchecked)
or when it overlaps a live peer's lock; else this agent's lock (insert or replace). An error leaves the db as it was
(the Lua's transaction rolls back). -/
def lock (c : Tasks.Ctx) (path reason lease : String) (db0 : Db) : Db × Except String Unit :=
  if let some (.ended ..) := fence db0 c.me c.here then (db0, .error s!"{c.me} was ended; `swarm join` to return.") else
  let db := touch db0 c.me none c.here c.now
  match (others db c.me c.now).find? fun o => overlaps path o.path with
  | some o => (db0, .error s!"{path} overlaps {o.path}, locked by {o.agent.getD ""}; message it")
  | none => match dur lease with
    | none => (db0, .error s!"bad duration '{lease}' (use 90s, 30m, 2h)")
    | some l =>
      let row : Lock := { path, agent := some c.me, reason := some reason, since := some c.now,
                          lease_until := some (c.now + l), seen := some 0 }
      let db := { db with locks := db.locks.filter (fun (x : Lock) => x.path != path) ++ [row] }
      (db.log c.now (some c.me) "lock" (some path) (some reason), .ok ())

/-- `swarm unlock`: drops this agent's lock on `path`, if it has one. -/
def unlock (me path : String) (now : Int) (db : Db) : Db :=
  let db := { db with locks := db.locks.filter fun l => !(l.path == path && l.agent == some me) }
  db.log now (some me) "unlock" (some path) none

end SwarmLean.Locks

import SwarmLean.Db.Tasks

/-! spawn's steps: agents.reserve (the max check and the new row, before the launch), tasks.reserve (that and the
task's claim) and tasks.unreserve (a launch that failed). -/

namespace SwarmLean.Spawn
open Agents Tasks

/-- The max check and the new agent's row, in one transaction so two spawns can't both take the last place
(agents.reserve). -/
def reserveAgent (db : Db) (envComms : Option String) (name cwd : String) (model : Option String) (now : Int) :
    Except Refusal Db :=
  if (live db).any (·.name == name) then .error (.die s!"{name} is a live agent") else
  let (n, _, mx) := limits db envComms
  match mx with
  | some x => if (n : Int) ≥ x then .error (.refused s!"{n} agents are live and the user's max is {x}. The communicator can raise it (`swarm limits --max N`).") else go
  | none => go
where
  go : Except Refusal Db :=
    let db := if db.agents.any (·.name == name) then db else
      { db with agents := db.agents ++ [{ name, cwd := some cwd, status := some "idle", last_active := some now, started := some now }] }
    .ok ((newInbox db name).setAgent name fun a =>
      { a with hc := none, ended := none, status := some "idle", model := model.orElse fun _ => a.model })

/-- agents.reserve as a step: the db unchanged on a refusal. -/
def reserve (db : Db) (envComms : Option String) (name cwd : String) (model : Option String) (now : Int) :
    Db × Except Refusal Unit :=
  match reserveAgent db envComms name cwd model now with
  | .ok db' => (db', .ok ())
  | .error e => (db, .error e)

/-- Reserves the agent and claims task `tid` for it, the task row as it was returned; `top` (auto-spawn): the claim
holds only while `tid` still heads the pool (tasks.reserve, inside cmd_spawn's transaction). -/
def reserveTask (db : Db) (envComms : Option String) (name cwd : String) (tid : Int) (model : Option String) (now : Int)
    (top : Option (Db → Option Int) := none) : Db × Except Refusal Task :=
  match go with
  | .ok (db', r) => (db', .ok r)
  | .error e => (db, .error e)
where
  go : Except Refusal (Db × Task) := do
    if let some f := top then
      if f db != some tid then throw (.lost s!"task #{d tid} no longer heads the pool")
    let db ← reserveAgent db envComms name cwd model now
    let some r := db.find tid | throw (.die s!"no task #{d tid}")
    let u := undone db r
    if !u.isEmpty then throw (.die s!"#{d tid} waits on {idsText (u.map (·.id : Task → Int))}")
    if r.state ≠ .open then throw (.lost s!"task #{d tid} is {r.state.text}{owned r}")
    if stopPending db r then throw (.lost s!"task #{d tid} waits for {r.stop_to.getD "nil"} to read its stop")
    let db := db.set tid fun t => { t with state := .claimed, owner := some name, lease_until := some (now + LEASE),
                                           first_claimed_at := t.first_claimed_at.orElse fun _ => some now }
    pure (db.log now (some name) "claim" none (some s!"#{d tid} {r.title.getD ""}"), r)

/-- `reserveTask` on a slice that also holds other swarms' agents (the stop holders of the tasks read: agent names are
the machine's); `own` names the swarm's live agents. The max counts only the swarm's; the stop guard and `top` see
every row (board #124). -/
def reserveTaskAmong (own : List String) (db : Db) (envComms : Option String) (name cwd : String) (tid : Int)
    (model : Option String) (now : Int) (top : Option (Db → Option Int) := none) : Db × Except Refusal Task :=
  let other := db.agents.filter fun a => !own.contains a.name && a.name != name
  let mine := db.agents.filter fun a => !other.any (·.name == a.name)
  match reserveTask { db with agents := mine } envComms name cwd tid model now (top.map fun f _ => f db) with
  | (_, .error e) => (db, .error e)
  | (db', .ok r) =>
    if stopPending db r then (db, .error (.lost s!"task #{d tid} waits for {r.stop_to.getD "nil"} to read its stop"))
    else ({ db' with agents := db'.agents ++ other }, .ok r)

/-- A launch that failed: reopens the task `r` it reserved if the new agent still holds it (tasks.unreserve), then ends
the row as every end does (`endRow`: its stay, claims, locks, conflicts and pair keys go; a launch that failed late may
have run the agent long enough to take one), unless a terminal bound it meanwhile. -/
def unreserve (db : Db) (name : String) (r : Option Task) (now : Int) : Db :=
  let db := match r with
    | none => db
    | some r => db.set r.id fun t =>
      if t.owner == some name && t.state = .claimed then
        { t with state := .open, owner := none, lease_until := none, first_claimed_at := r.first_claimed_at } else t
  if (db.agent name).any (·.hc.isNone) then endRow db name now else db

end SwarmLean.Spawn

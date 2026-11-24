import SwarmLean.Db.Tasks

/-! Places, Ready and Backlog (board #128, Linear's states): every task not closed has a place (`Task.pos`); Ready's
tasks in place order are the staffing order, Backlog's are its order. `queue add`/`queue rm` move a task's place and
change nothing else; `task backlog` and `task ready` move it between the two, to the end. `staffing` is the order in
which auto-spawn and an agent asking for work take tasks: the red main's tasks first, then Ready by place, never a task
reserved for an assignee. -/

namespace SwarmLean.Queue
open Tasks Agents

/-- `l` without repeats, each id at its first place. -/
def dedup : List Int → List Int
  | [] => []
  | x :: xs => x :: (dedup xs).filter (· != x)

/-- The places become `l`: each task of `l` gets its place 1..n, every other task none (ids of no task and repeats
are dropped first). -/
def setQueue (db : Db) (l : List Int) : Db :=
  let l := dedup (l.filter fun i => (db.find i).isSome)
  { db with tasks := db.tasks.map fun t => { t with pos := (l.idxOf? (t.id : Int)).map fun (i : Nat) => (i : Int) + 1 } }

/-- Order by place, then id. -/
def qLe (a b : Task) : Bool := a.pos.getD 0 < b.pos.getD 0 || (a.pos.getD 0 == b.pos.getD 0 && a.id ≤ b.id)

/-- The tasks with a place, in place order. -/
def queued (db : Db) : List Task := (db.tasks.filter (·.pos.isSome)).mergeSort qLe

/-- Their ids, in place order. -/
def queueOf (db : Db) : List Int := (queued db).map fun t => (t.id : Int)

/-- Ready's tasks, in place order: the staffing order before deps, stops and reservations. -/
def readyList (db : Db) : List Task := (queued db).filter (·.status = .ready)

/-- Backlog's tasks, in place order. -/
def backlogList (db : Db) : List Task := (queued db).filter (·.status = .backlog)

/-- A Ready or Backlog task's place in its list, 1..n ("Queue N" on the board). -/
def place (db : Db) (t : Task) : Option Nat :=
  let l := if t.status = .ready then readyList db else if t.status = .backlog then backlogList db else []
  (l.findIdx? (·.id == t.id)).map (· + 1)

/-- On the board: not closed. -/
def onBoard (t : Task) : Bool := !t.status.closed

/-- Not started yet: Backlog or Ready, the tasks a place move, `task assign` and `task after` act on. -/
def unstarted (t : Task) : Bool := t.status = .ready || t.status = .backlog

/-- Takes the places of the tasks that closed (completed, cancelled). -/
def tidy (db : Db) : Db :=
  { db with tasks := db.tasks.map fun t => if onBoard t || t.pos.isNone then t else { t with pos := none } }

/-- Task `id` moved to the end of the places (of Ready, of Backlog). -/
def toEnd (id : Int) (db : Db) : Db := let e := endPos db; db.set id ({ · with pos := some e })

/-- The checks of `queue add`: tasks in Ready or Backlog; a place other than the end only by the communicator or the
user; `--before`/`--after` a task with a place, not among the ids. -/
def addCheck (c : Ctx) (ids : List Int) (w : Place) (db : Db) : Except String Unit := do
  for i in ids do
    match db.find i with
    | none => throw s!"no task #{d i}"
    | some r => if !unstarted r then throw s!"task #{d i} is {r.status.name}; only a Ready or Backlog task has a place"
  if !inCharge db c.comms c.me then
    if let .back := w then pure () else throw "only the communicator or the user can move a task other than to the end"
  match w with
  | .before x | .after x =>
    if ids.contains x then throw s!"#{d x} can't be placed next to itself"
    match db.find x with
    | some r => if !unstarted r then throw s!"#{d x} is {r.status.name}; it has no place in Ready or Backlog"
    | none => throw s!"no task #{d x}"
  | _ => pure ()

/-- The `task-place` event: task `i`'s place in its list before and after. -/
def logPlace (c : Ctx) (db0 db : Db) (i : Int) : Db :=
  let at_ (db : Db) := ((db.find i).bind (place db)).map (d ·) |>.getD "-"
  db.log c.now (some c.me) "task-place" none (some s!"#{d i} {at_ db0} {at_ db}")

/-- `queue add`: puts `ids`, in their order, at `w` (the end: of the places); nothing else on the task changes. -/
def add (c : Ctx) (ids : List Int) (w : Place) (db : Db) : Db × Except String Unit :=
  match addCheck c ids w db with
  | .error e => (db, .error e)
  | .ok () =>
    let ids := dedup ids
    let db1 := match w with
      | .back => ids.foldl (fun db i => toEnd i db) db
      | _ =>
        let rest := (queueOf db).filter (!ids.contains ·)
        let n := match w with
          | .front => 0
          | .before x => rest.idxOf x
          | .after x => rest.idxOf x + 1
          | .back => rest.length
        setQueue db (rest.take n ++ ids ++ rest.drop n)
    (ids.foldl (logPlace c db) db1, .ok ())

/-- `queue rm`: moves `ids` to the end of the places; nothing else on the task changes. -/
def rm (c : Ctx) (ids : List Int) (db : Db) : Db × Except String Unit := add c ids .back db

/-- `task backlog`: Ready task `id` moves to the end of Backlog with note `note` (a Backlog task's note is
replaced); its assignee kept. Auto-spawn and an agent asking for work skip it until `task ready`. -/
def backlog (c : Ctx) (id : Int) (note : String) (db : Db) : Db × Except String Unit :=
  match db.find id with
  | none => (db, .error s!"no task #{d id}")
  | some r =>
    if !unstarted r then
      (db, .error s!"task #{d id} is {r.status.name}; only a Ready task moves to Backlog{if r.status.category = .started then " (release it first)" else ""}")
    else if strip note == "" then (db, .error "--note is empty: say what the task waits for")
    else
      let db1 := db.set id ({ · with state := .backlog r.assignee, note := some (oneLine note) })
      let db1 := if r.status = .ready then toEnd id db1 else db1
      (db1.log c.now (some c.me) "task-backlog" none (some s!"#{d id} {oneLine note}"), .ok ())

/-- `task ready`: Backlog task `id` moves to the end of Ready, its note and assignee kept; by the communicator or the
user only. -/
def ready (c : Ctx) (id : Int) (db : Db) : Db × Except String Unit :=
  match db.find id with
  | none => (db, .error s!"no task #{d id}")
  | some r =>
    if r.status ≠ .backlog then (db, .error s!"task #{d id} is {r.status.name}; only a Backlog task moves to Ready")
    else inChargeStep c s!"move #{d id} to Ready" "task-ready" s!"#{d id}"
      (fun db => toEnd id (db.set id ({ · with state := .ready r.assignee }))) db

/-- `task assign`: Ready or Backlog task `id` reserved for `who` (none: no assignee); by the communicator or the user
only. Auto-spawn skips a reserved task, and only its assignee claims it (or the communicator's --force). -/
def assign (c : Ctx) (id : Int) (who : Option String) (db : Db) : Db × Except String Unit :=
  match db.find id with
  | none => (db, .error s!"no task #{d id}")
  | some r =>
    let who := who.bind fun w => py (some (strip w))
    if !unstarted r then
      (db, .error s!"task #{d id} is {r.status.name}; only a Ready or Backlog task is assigned (a claim assigns a started one)")
    else inChargeStep c s!"assign #{d id}" "task-assign" s!"#{d id} {who.getD "-"}"
      (·.set id ({ · with state := if r.status = .backlog then .backlog who else .ready who })) db

/-- Staffed by auto-spawn and offered to an agent asking for work: no assignee reserves it. -/
def free (t : Task) : Bool := t.assignee.isNone

/-- Startable `main red:` tasks no one is assigned, in pool order. -/
def staffRed (db : Db) : List Task := (pool db).filter fun t => free t && redKey t == 1

/-- Startable Ready tasks no one is assigned (no red one), in place order. -/
def staffReady (db : Db) : List Task := (pool db).filter fun t => free t && redKey t == 0

/-- The tasks to staff, in order: a red main's task, then Ready by place; never a Backlog task, one waiting on a
dependency or one reserved for an assignee. Auto-spawn staffs from it and an idle agent is told of it. -/
def staffing (db : Db) : List Task := staffRed db ++ staffReady db

/-- Auto-spawn's next task: the first of `staffing` it has not given up on (`skip`). -/
def staffHead (skip : Task → Bool) (db : Db) : Option Int := ((staffing db).find? (!skip ·)).map fun t => (t.id : Int)

/-- Why a task with a place is not staffed now; none when it would be. -/
def whyNot (db : Db) (t : Task) : Option String :=
  if t.status = .backlog then some s!"backlog{match t.note with | some n => ": " ++ n | none => ""}"
  else if t.status ≠ .ready then some s!"{t.status.name}{match py t.assignee with | some a => " by " ++ a | none => ""}"
  else if let some a := py t.assignee then some s!"assigned to {a}"
  else if (pool db).any (·.id == t.id) then none
  else match undone db t with
    | [] => if stopPending db t then some s!"waits for {t.stop_to.getD "nil"} to read its stop" else some t.status.name
    | u => some ("waiting on " ++ idsText (u.map fun x => (x.id : Int)) ++
        if u.any (·.status.category = .cancelled) then " (cancelled)" else "")

/-- `task done`, and a completed task's place goes; the count is of the tasks to staff after it. -/
def done (c : Ctx) (id : Int) (evidence : String) (db : Db) : Db × Except String DoneOut :=
  match Tasks.done c id evidence db with
  | (db', .ok (.done k st _)) => let db' := tidy db'; (db', .ok (.done k st (staffing db').length))
  | (db', .ok (.landed o)) => (tidy db', .ok (.landed o))
  | r => r

/-- `task drop`, and its place goes. -/
def drop (c : Ctx) (id : Int) (dup : Option Int) (note : Option String) (db : Db) : Db × Except String (List Task) :=
  match Tasks.drop c id dup note db with
  | (db', .ok ws) => (tidy db', .ok ws)
  | r => r

end SwarmLean.Queue

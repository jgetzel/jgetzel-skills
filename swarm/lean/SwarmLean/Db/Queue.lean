import SwarmLean.Db.Tasks

/-! The staffing queue and holds (board #128): an ordered list of tasks that auto-spawn staffs from, finer than
priority, and holds that keep a task from being staffed. A queued task's `qpos` is its place, 1..n; `setQueue` is the
one step that writes them. `staffing` is the order in which auto-spawn and an agent asking for work take tasks. -/

namespace SwarmLean.Queue
open Tasks Agents

/-- `l` without repeats, each id at its first place. -/
def dedup : List Int → List Int
  | [] => []
  | x :: xs => x :: (dedup xs).filter (· != x)

/-- The queue becomes `l`: each task of `l` gets its place 1..n, every other task leaves the queue (ids of no task and
repeats are dropped first). -/
def setQueue (db : Db) (l : List Int) : Db :=
  let l := dedup (l.filter fun i => (db.find i).isSome)
  { db with tasks := db.tasks.map fun t => { t with qpos := (l.idxOf? (t.id : Int)).map fun (i : Nat) => (i : Int) + 1 } }

/-- Order by place in the queue. -/
def qLe (a b : Task) : Bool := a.qpos.getD 0 ≤ b.qpos.getD 0

/-- The queued tasks, in queue order. -/
def queued (db : Db) : List Task := (db.tasks.filter (·.qpos.isSome)).mergeSort qLe

/-- The queued tasks' ids, in queue order. -/
def queueOf (db : Db) : List Int := (queued db).map fun t => (t.id : Int)

/-- On the board: open, claimed or blocked. -/
def onBoard (t : Task) : Bool := t.state = .open || t.state = .claimed || t.state = .blocked

/-- Takes the tasks that left the board (done, dropped) out of the queue and closes the gaps. -/
def tidy (db : Db) : Db := setQueue db ((queueOf db).filter fun i => (db.find i).any onBoard)

/-- Who queued task `id`: the agent of its latest `queue` event. -/
def queuer (db : Db) (id : Int) : Option String :=
  ((taskEvents db id.toNat).filter (·.kind == some "queue")).getLast?.bind (·.agent)

/-- Where `queue add` puts its ids. -/
inductive Place
  | back
  | front
  | before (id : Int)
  | after (id : Int)

/-- The checks of `queue add`: tasks on the board; a place other than the back, or moving an entry another agent
queued, only by the communicator or the user; `--before`/`--after` a queued task not among the ids. -/
def addCheck (c : Ctx) (ids : List Int) (w : Place) (db : Db) : Except String Unit := do
  let q := queueOf db
  for i in ids do
    match db.find i with
    | none => throw s!"no task #{d i}"
    | some r => if !onBoard r then throw s!"task #{d i} is {r.state.text}; only a task on the board can be queued"
  if !inCharge db c.comms c.me then
    if let .back := w then pure () else throw "only the communicator or the user can queue other than at the back"
    for i in ids do
      if q.contains i && queuer db i != some c.me then
        throw s!"#{d i} was queued by {(queuer db i).getD "nil"}; only it, the communicator or the user can move it"
  match w with
  | .before x | .after x =>
    if ids.contains x then throw s!"#{d x} can't be placed next to itself"
    if !q.contains x then throw s!"#{d x} is not queued"
  | _ => pure ()

/-- `queue add`: puts `ids`, in their order, at `w`; an id already queued moves. -/
def add (c : Ctx) (ids : List Int) (w : Place) (db : Db) : Db × Except String Unit :=
  match addCheck c ids w db with
  | .error e => (db, .error e)
  | .ok () =>
    let ids := dedup ids
    let rest := (queueOf db).filter (!ids.contains ·)
    let n := match w with
      | .back => rest.length
      | .front => 0
      | .before x => rest.idxOf x
      | .after x => rest.idxOf x + 1
    let db := setQueue db (rest.take n ++ ids ++ rest.drop n)
    (ids.foldl (fun db i => db.log c.now (some c.me) "queue" none (some s!"#{d i}")) db, .ok ())

/-- `queue rm`: takes `ids` out of the queue; an entry another agent queued only by the communicator or the user. -/
def rm (c : Ctx) (ids : List Int) (db : Db) : Db × Except String Unit :=
  let q := queueOf db
  match ids.find? (!q.contains ·) with
  | some i => (db, .error s!"#{d i} is not queued")
  | none =>
    match ids.find? fun i => !inCharge db c.comms c.me && queuer db i != some c.me with
    | some i => (db, .error s!"#{d i} was queued by {(queuer db i).getD "nil"}; only it, the communicator or the user can take it out")
    | none =>
      let db := setQueue db (q.filter (!ids.contains ·))
      (ids.foldl (fun db i => db.log c.now (some c.me) "unqueue" none (some s!"#{d i}")) db, .ok ())

/-- `task hold`: the task is never staffed until `task unhold`. -/
def hold (c : Ctx) (id : Int) (why : String) (db : Db) : Db × Except String Unit :=
  match db.find id with
  | none => (db, .error s!"no task #{d id}")
  | some r =>
    if !onBoard r then (db, .error s!"task #{d id} is {r.state.text}; only a task on the board can be held")
    else if strip why == "" then (db, .error "--why is empty: say what the task waits for")
    else
      let db := db.set id ({ · with hold := some (oneLine why) })
      (db.log c.now (some c.me) "hold" none (some s!"#{d id} {oneLine why}"), .ok ())

/-- `task unhold`. -/
def unhold (c : Ctx) (id : Int) (db : Db) : Db × Except String Unit :=
  match db.find id with
  | none => (db, .error s!"no task #{d id}")
  | some r =>
    if r.hold.isNone then (db, .error s!"task #{d id} is not held")
    else
      let db := db.set id ({ · with hold := none })
      (db.log c.now (some c.me) "unhold" none (some s!"#{d id}"), .ok ())

/-- Held from staffing. -/
def held (t : Task) : Bool := t.hold.isSome

/-- The `swarm limits --queue-only` switch: unqueued tasks are backlog. -/
def queueOnly (db : Db) : Bool := ((db.getMeta "queue_only").bind (·.v)) == some "on"

/-- Startable `main red:` tasks not held, in pool order. -/
def staffRed (db : Db) : List Task := (pool db).filter fun t => !held t && redKey t == 1

/-- Startable queued tasks not held (no red one), in queue order. -/
def staffQueue (db : Db) : List Task :=
  ((pool db).filter fun t => !held t && redKey t == 0 && t.qpos.isSome).mergeSort qLe

/-- Startable unqueued tasks not held (no red one), in pool order; none with queue-only on. -/
def staffRest (db : Db) : List Task :=
  if queueOnly db then [] else (pool db).filter fun t => !held t && redKey t == 0 && t.qpos.isNone

/-- The tasks to staff, in order: a red main's task, then the queue, then (queue-only off) the rest by priority; never
a held one. Auto-spawn staffs from it and an idle agent is told of it. -/
def staffing (db : Db) : List Task := staffRed db ++ staffQueue db ++ staffRest db

/-- Auto-spawn's next task: the first of `staffing` it has not given up on (`skip`). -/
def staffHead (skip : Task → Bool) (db : Db) : Option Int := ((staffing db).find? (!skip ·)).map fun t => (t.id : Int)

/-- Why a queued task is not staffed now; none when it would be. -/
def whyNot (db : Db) (t : Task) : Option String :=
  if let some h := t.hold then some s!"held: {h}"
  else if t.state = .claimed then some s!"claimed by {(py t.owner).getD "-"}"
  else if t.state = .blocked then some s!"blocked by {(py t.owner).getD "-"}"
  else if (pool db).any (·.id == t.id) then none
  else match undone db t with
    | [] => if stopPending db t then some s!"waits for {t.stop_to.getD "nil"} to read its stop" else some t.state.text
    | u => some ("waits on " ++ idsText (u.map fun x => (x.id : Int)))

/-- `task done`, and the task leaves the queue; the count is of the tasks to staff after it. -/
def done (c : Ctx) (id : Int) (evidence : String) (db : Db) : Db × Except String DoneOut :=
  match Tasks.done c id evidence db with
  | (db', .ok (.done k st _)) => let db' := tidy db'; (db', .ok (.done k st (staffing db').length))
  | r => r

/-- `task drop`, and the task leaves the queue. -/
def drop (c : Ctx) (id : Int) (db : Db) : Db × Except String (List Task) :=
  match Tasks.drop c id db with
  | (db', .ok ws) => (tidy db', .ok ws)
  | r => r

end SwarmLean.Queue

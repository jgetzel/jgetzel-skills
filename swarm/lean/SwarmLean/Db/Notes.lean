import SwarmLean.Db.Tasks

/-! Notes to a task (board #202): `swarm post '#N' <text>`. A note is logged on task N (a `task-note` event) and
delivered: to the task's live owner, held for its next owner, or for a done task to whoever did it, else the
communicator. A held note is a message to the name `#N`; the next claim of N (or the spawn it is reserved for) takes
the unread ones with one `take`, so the inbox theorems (Proofs/Msgs.lean) cover it as a `swarm read` of `#N`. -/

namespace SwarmLean.Notes
open Msgs Tasks Agents

/-- The name task `id`'s held notes are addressed to. -/
def box (id : Int) : String := "#" ++ d id

/-- The task a `post` target names: `#N` or `task:N`. -/
def target? (s : String) : Option Int :=
  let r := if s.startsWith "#" then some (s.drop 1).toString
    else if s.startsWith "task:" then some (s.drop 5).toString else none
  r.bind fun x => if !x.isEmpty && x.all Char.isDigit then x.toNat?.map Int.ofNat else none

/-- Where a note to a task goes. -/
inductive Dest
  /-- the task's live owner -/
  | owner (o : String)
  /-- the poster holds the task: only recorded -/
  | self
  /-- held for the task's next owner -/
  | held
  /-- a done (or dropped) task: whoever did it, still live -/
  | doer (o : String) (st : Status)
  /-- a done (or dropped) task whose doer has ended: the communicator -/
  | comms (c : String) (st : Status)
  /-- as `comms`, but there is no communicator other than the poster: only recorded -/
  | none (st : Status)
  deriving DecidableEq, Repr

/-- Where a note from `me` to task `t` goes (a landing task's to its owner, as a claimed one's), `here o` saying whether agent `o` is live with its terminal up and
`comms` naming the communicator. Every state is named, so a new one must say where its notes go. -/
def dest (here : String → Bool) (comms : Option String) (me : String) (t : Task) : Dest :=
  let gone (st : Status) : Dest := match comms with
    | some c => if c == me then .none st else .comms c st
    | Option.none => .none st
  let ended (st : Status) : Dest := match t.owner with
    | some o => if o != me && here o then .doer o st else gone st
    | Option.none => gone st
  match t.status with
  | .inProgress | .needsInput | .inReview => match t.owner with
    | some o => if o == me then .self else if here o then .owner o else .held
    | Option.none => .held
  | .backlog | .ready => .held
  | .completed => ended .completed
  | .cancelled => ended .cancelled
  | .duplicate => ended .duplicate

/-- What `post` tells the poster of where note to task `id` went. -/
def Dest.text (id : Int) : Dest → String
  | .owner o => s!"to {o}"
  | .self => s!"recorded on #{d id} (you hold it)"
  | .held => s!"held for #{d id}'s next owner"
  | .doer o st => s!"to {o}: #{d id} is {st.name}"
  | .comms _ st => s!"to comms: #{d id} is {st.name}"
  | .none st => s!"recorded on #{d id} only: it is {st.name}, whoever did it has ended and there is no other communicator"

/-- The message a note sends, if any: its addressee and body. -/
def Dest.msg (id : Int) (text : String) : Dest → Option (Msgs.Dest × String)
  | .owner o => some (Msgs.Dest.agent o, s!"[#{d id}] {text}")
  | .held => some (Msgs.Dest.task id.toNat, text)
  | .doer o st => some (Msgs.Dest.agent o, s!"[#{d id}, {st.name}] {text}")
  | .comms c st => some (Msgs.Dest.agent c, s!"[#{d id} is {st.name}] {text}")
  | .self | .none _ => Option.none

/-- Where a delivered note went, as its event's path. -/
def Dest.path (id : Int) : Dest → Option String
  | .owner o | .doer o _ | .comms o _ => some o
  | .held => some (box id)
  | .self | .none _ => Option.none

/-- `swarm post '#N' <text>` from `frm` (board #202): the note logged on task `id` (event `task-note`, the whole text)
and sent where `dest` says. -/
def post (db : Db) (now : Int) (frm : String) (id : Int) (text : String) (urgent : Bool) (here : String → Bool)
    (comms : Option String) : Db × Except String Dest :=
  match db.find id with
  | Option.none => (db, .error s!"no task #{d id}")
  | some t =>
    let to := dest here comms frm t
    let db := match to.msg id text with
      | some (who, body) =>
        let kind := match who with | .task _ => some "task-note" | _ => Option.none
        (Msgs.post db now (Msgs.Who.ofText frm) who body urgent kind).1
      | Option.none => db
    (db.log now (some frm) "task-note" (to.path id) (some s!"#{d id} {text}"), .ok to)

/-- Task `id`'s held notes, marked read: one `take` of `#N` (whose rows past its cursor include the `@all` ones,
read past and not shown), logged as `task-notes-given` to `who` when there were any. -/
def takeHeld (who : String) (now : Int) (id : Int) (db : Db) : Db × List Msg :=
  let (db, _, fit) := take (box id) _root_.id db
  let ns := fit.filter (·.dest == some (box id))
  if ns.isEmpty then (db, ns)
  else (db.log now (some who) "task-notes-given" (some who) (some s!"#{d id} {ns.length}"), ns)

/-- Task `id`'s held notes still unread, by id. -/
def held (db : Db) (id : Int) : List Msg := (unread db (box id)).filter (·.dest == some (box id))

/-- A note as `task show` lists it. -/
structure Note where
  ts : Int
  frm : String
  text : String
  /-- the agent it was sent to, `#N` when held, none when only recorded -/
  to : Option String
  /-- held and not yet given to an owner -/
  held : Bool

/-- Task `id`'s notes, oldest first: its `task-note` events, a held one given once a later `task-notes-given` is. -/
def notes (db : Db) (id : Int) : List Note :=
  let mine (k : String) (e : Event) : Bool := e.kind == some k && eventTask e == some id.toNat
  let given := (db.events.filter (mine "task-notes-given")).foldl (fun m e => max m e.id) 0
  (db.events.filter (mine "task-note")).map fun e =>
    let data := e.data.getD ""
    let text := (data.drop ((box id).length + 1)).toString
    { ts := e.ts.getD 0, frm := e.agent.getD "", text, to := e.path,
      held := e.path == some (box id) && e.id > given }

end SwarmLean.Notes

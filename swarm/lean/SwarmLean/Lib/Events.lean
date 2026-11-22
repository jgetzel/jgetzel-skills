import SwarmLean.Lib.Swarms
import SwarmLean.Lib.Json
import SwarmLean.Db.Tasks

/-! The machine's event log, read by key (sw-global §3) for the Herdr swarm view: a task's activity (`task show
--json`) and the events after an id (`swarm events --since`). -/

namespace SwarmLean.Events
open Lean (Json)
open Sqlite (Val)

/-- The columns read, in `ofRow`'s order. -/
def COLS : String := "id, ts, swarm, repo, agent, kind, path, data"

/-- An event row of the machine's db, with its swarm and repo. -/
structure Ev where
  ev : Event
  swarm : Option String := none
  repo : Option String := none

/-- A row of `COLS`. -/
def ofRow (r : Array Val) : Option Ev :=
  (Swarms.int r[0]?).map fun id =>
    { ev := { id := id.toNat, ts := Swarms.int r[1]?, agent := Swarms.txt r[4]?, kind := Swarms.txt r[5]?,
              path := Swarms.txt r[6]?, data := Swarms.txt r[7]? },
      swarm := py (Swarms.txt r[2]?), repo := py (Swarms.txt r[3]?) }

/-- An event's data past its task's `#<id> ` (or `auto #<id> `): what happened, without the task's number. -/
def text (e : Event) : Option String :=
  e.data.map fun s =>
    let r := if s.startsWith "auto #" then (s.drop 6).toString else if s.startsWith "#" then (s.drop 1).toString else s
    let ds := r.toList.takeWhile Char.isDigit
    if ds.isEmpty || r == s then s else String.ofList ((r.toList.drop ds.length).dropWhile (· == ' '))

/-- An event of task `id`'s activity: its kind as the activity names it (`Tasks.shortKind`), the raw kind, who and what. -/
def taskJson (x : Ev) : Json :=
  let e := x.ev
  let k := e.kind.getD ""
  Json.mkObj [("id", Json.int e.id), ("ts", Json.oint e.ts), ("kind", .str (Tasks.shortKind k)), ("raw", .str k),
    ("agent", Json.ostr e.agent), ("swarm", Json.ostr x.swarm),
    ("text", Json.ostr (if k == "task-blocked" then e.data else text e))]

/-- An event as `swarm events` prints it: its columns, and the task it is about, if any. -/
def json (x : Ev) : Json :=
  let e := x.ev
  let task : Option Int := if e.kind == some "task-blocked" then e.path.bind parseInt else (Tasks.eventTask e).map fun i => (i : Int)
  Json.mkObj [("id", Json.int e.id), ("ts", Json.oint e.ts), ("swarm", Json.ostr x.swarm), ("repo", Json.ostr x.repo),
    ("agent", Json.ostr e.agent), ("kind", Json.ostr e.kind), ("path", Json.ostr e.path), ("data", Json.ostr e.data),
    ("task", Json.oint task)]

variable {m : Type → Type} [Monad m] [Env m] [Sys m]

/-- The events about task `id`, oldest first: the `Tasks.SHOW_KINDS` events whose data starts with `#<id>` (or `auto
#<id>`) and its `task-blocked` ones; one select on the event_kind index. -/
def ofTask (id : Int) : m (List Ev) := do
  let n := "#" ++ d id
  let a := "auto " ++ n
  let ks := Tasks.SHOW_KINDS
  let rs ← Sys.sqlAt (← Swarms.dbPath) schema [(s!"select {COLS} from event where kind in ({", ".intercalate (ks.map fun _ => "?")}) " ++
      "and (data=? or substr(data, 1, ?)=? or data=? or substr(data, 1, ?)=? or (kind='task-blocked' and path=?)) order by id",
    ks.map Val.text ++ ([.text n, .int (n.length + 1), .text (n ++ " "), .text a, .int (a.length + 1), .text (a ++ " "),
      .text (d id)] : List Val))] true
  return (rs.headD #[]).toList.filterMap ofRow

/-- The events after id `since` (none: the newest `limit`), at most `limit`, oldest first; and the log's last id. -/
def since (since : Option Int) (limit : Nat) : m (List Ev × Int) := do
  let rs ← Sys.sqlAt (← Swarms.dbPath) schema [("select coalesce(max(id), 0) from event", []),
    (s!"select {COLS} from event where id > ? order by id limit ?", [.int (since.getD 0), .int limit]),
    (s!"select {COLS} from event order by id desc limit ?", [.int limit])] true
  let last := ((rs.headD #[])[0]?.bind (Swarms.int ·[0]?)).getD 0
  let evs := match since with
    | some _ => ((rs.getD 1 #[]).toList.filterMap ofRow)
    | none => ((rs.getD 2 #[]).toList.filterMap ofRow).reverse
  return (evs, last)

end SwarmLean.Events

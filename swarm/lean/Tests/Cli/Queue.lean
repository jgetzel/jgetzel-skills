import Tests.Cli.Spawn

/-! Board #128: `swarm queue`, `task hold`/`unhold`, `limits --queue-only`, and the staffing order auto-spawn takes. -/

namespace SwarmLean.Tests.Cli.Queue
open SwarmLean.Tests.Cli
open SwarmLean.Tests.Cli.Spawn (tick twoHaiku)
open Lean (Json toJson)

/-- The queue's ids in order, from the db. -/
def order (t : T) : IO (List Json) := return (← t.q "select id from task where qpos is not null order by qpos").toList.map (·.f "id")

/-- The places, in order: 1..n with no gap. -/
def placesOk (t : T) : IO Unit := do
  let ps := (← t.q "select qpos from task where qpos is not null order by qpos").toList.map (·.f "qpos")
  eq ps ((List.range ps.length).map fun i => toJson (i + 1))

def adds (t : T) (n : Nat) : IO Unit := for i in List.range n do t.sw_ "comms" ["task", "add", s!"t{i + 1}"]

def test_queue_add_appends_moves_and_places (t : T) : IO Unit := do
  t.q_ "insert or replace into meta(k,v) values('comms','comms')"
  adds t 4
  has (← t.sw "comms" ["queue"]).stdout "(queue empty)"
  has (← t.sw "comms" ["queue", "add", "3", "1"]).stdout "queued #3, #1"
  eq (← order t) [toJson 3, toJson 1]
  t.sw_ "comms" ["queue", "add", "4", "--front"]
  eq (← order t) [toJson 4, toJson 3, toJson 1]
  t.sw_ "comms" ["queue", "add", "1", "--before", "3"]  -- a queued id moves
  eq (← order t) [toJson 4, toJson 1, toJson 3]
  t.sw_ "comms" ["queue", "add", "2", "--after", "4"]
  eq (← order t) [toJson 4, toJson 2, toJson 1, toJson 3]
  t.sw_ "comms" ["queue", "add", "4"]  -- append moves it to the back
  eq (← order t) [toJson 2, toJson 1, toJson 3, toJson 4]
  placesOk t
  let out := (← t.sw "comms" ["queue"]).stdout
  has out "1. #2 open    startable  t2"
  has out "4. #4 open    startable  t4"
  t.sw_ "comms" ["queue", "rm", "1", "3"]
  eq (← order t) [toJson 2, toJson 4]
  placesOk t
  has (← t.sw "comms" ["queue", "rm", "1"] { ok := false }).stderr "#1 is not queued"
  has (← t.sw "comms" ["queue", "add", "9"] { ok := false }).stderr "no task #9"
  has (← t.sw "comms" ["queue", "add", "1", "--before", "3"] { ok := false }).stderr "#3 is not queued"
  has (← t.sw "comms" ["board"]).stdout "[queue 1]"
  has (← t.sw "comms" ["task", "show", "4"]).stdout "queue: 2"

def test_queue_rights (t : T) : IO Unit := do
  t.q_ "insert or replace into meta(k,v) values('comms','comms')"
  adds t 3
  t.sw_ "a" ["queue", "add", "1"]  -- any agent may append
  t.sw_ "b" ["queue", "add", "2"]
  has (← t.sw "b" ["queue", "add", "3", "--front"] { ok := false }).stderr "only the communicator or the user"
  has (← t.sw "b" ["queue", "add", "1"] { ok := false }).stderr "#1 was queued by a"
  has (← t.sw "b" ["queue", "rm", "1"] { ok := false }).stderr "#1 was queued by a"
  eq (← order t) [toJson 1, toJson 2]
  t.sw_ "a" ["queue", "add", "1"]  -- its own entry: moves to the back
  eq (← order t) [toJson 2, toJson 1]
  t.sw_ "a" ["queue", "rm", "1"]
  t.sw_ "comms" ["queue", "rm", "2"]  -- the communicator: anyone's
  eq (← order t) ([] : List Json)
  t.sw_ "a" ["queue", "add", "3"]
  t.sw_ "a" ["queue", "add", "1", "--front"] { env := [("SWARM_NAME", none)] }  -- the user (no SWARM_NAME)
  eq (← order t) [toJson 1, toJson 3]

def test_queue_left_on_done_and_drop (t : T) : IO Unit := do
  t.q_ "insert or replace into meta(k,v) values('comms','comms')"
  adds t 3
  t.sw_ "comms" ["queue", "add", "1", "2", "3"]
  t.sw_ "comms" ["task", "drop", "2"]
  eq (← order t) [toJson 1, toJson 3]
  placesOk t
  t.sw_ "a" ["task", "claim", "1"]
  has (← t.sw "comms" ["queue"]).stdout "1. #1 claimed claimed by a  t1"
  t.sw_ "a" ["task", "done", "1", "--evidence", "abc"]
  eq (← order t) [toJson 3]
  placesOk t
  has (← t.sw "comms" ["queue", "add", "1"] { ok := false }).stderr "task #1 is done"

def test_queue_says_why_not_startable (t : T) : IO Unit := do
  t.q_ "insert or replace into meta(k,v) values('comms','comms')"
  adds t 3
  t.sw_ "comms" ["task", "after", "2", "1"]
  t.sw_ "comms" ["task", "hold", "3", "--why", "needs the user's call"]
  t.sw_ "comms" ["queue", "add", "2", "3", "1"]
  let out := (← t.sw "comms" ["queue"]).stdout
  has out "1. #2 open    waits on #1  t2"
  has out "2. #3 open    held: needs the user's call  t3"
  has out "3. #1 open    startable  t1"

def test_hold_and_claim (t : T) : IO Unit := do
  t.q_ "insert or replace into meta(k,v) values('comms','comms')"
  adds t 1
  has (← t.sw "a" ["task", "hold", "1", "--why", " "] { ok := false }).stderr "--why is empty"
  t.sw_ "a" ["task", "hold", "1", "--why", "waits for the API"]
  has (← t.sw "a" ["board"]).stdout "held: waits for the API"
  has (← t.sw "a" ["task", "show", "1"]).stdout "\nheld: waits for the API"
  has (← t.sw "a" ["task", "claim", "1"] { ok := false }).stderr "task #1 is held: waits for the API"
  has (← t.sw "a" ["task", "claim", "1", "--force"] { ok := false }).stderr "only the communicator or the user can --force it"
  t.sw_ "comms" ["task", "claim", "1", "--force"]
  eq ((← t.q1 "select owner from task where id=1").f "owner") "comms"
  t.sw_ "comms" ["task", "unhold", "1"]
  hasnt (← t.sw "a" ["board"]).stdout "held:"
  has (← t.sw "a" ["task", "unhold", "1"] { ok := false }).stderr "task #1 is not held"

/-- The task the one auto-spawned agent took (room for one: two live, the number 2). -/
def staffed (t : T) : IO Json := do
  tick t 2
  let r ← t.q "select id from task where owner='t-2'"
  return if r.size == 1 then r[0]!.f "id" else .null

def test_staffing_queue_beats_priority (t : T) : IO Unit := do
  t.fakes; twoHaiku t
  t.sw_ "t-comms" ["task", "add", "urgent", "-p", "0"]
  t.sw_ "t-comms" ["task", "add", "queued", "-p", "3"]
  t.sw_ "t-comms" ["queue", "add", "2"]
  eq (← staffed t) (toJson 2)

def test_staffing_skips_held (t : T) : IO Unit := do
  t.fakes; twoHaiku t
  t.sw_ "t-comms" ["task", "add", "urgent", "-p", "0"]
  t.sw_ "t-comms" ["task", "add", "queued"]
  t.sw_ "t-comms" ["task", "add", "plain", "-p", "1"]
  t.sw_ "t-comms" ["queue", "add", "2"]
  t.sw_ "t-comms" ["task", "hold", "2", "--why", "later"]
  t.sw_ "t-comms" ["task", "hold", "1", "--why", "later"]
  eq (← staffed t) (toJson 3)  -- the queue's only entry and the P0 are held: priority order over the rest

def test_staffing_queue_only (t : T) : IO Unit := do
  t.fakes; twoHaiku t
  t.sw_ "t-comms" ["task", "add", "backlog", "-p", "0"]
  has (← t.sw "t-comms" ["limits", "--queue-only", "on"]).stdout ", queue-only"
  eq (← staffed t) Json.null  -- unqueued tasks are backlog
  t.sw_ "t-comms" ["task", "add", "queued", "-p", "3"]
  t.sw_ "t-comms" ["queue", "add", "2"]
  eq (← staffed t) (toJson 2)
  t.sw_ "t-comms" ["limits", "--queue-only", "off"]
  hasnt (← t.sw "t-comms" ["limits"]).stdout "queue-only"

def test_staffing_queue_only_off_is_priority (t : T) : IO Unit := do
  t.fakes; twoHaiku t
  t.sw_ "t-comms" ["task", "add", "low", "-p", "3"]
  t.sw_ "t-comms" ["task", "add", "high", "-p", "0"]
  eq (← staffed t) (toJson 2)

def test_staffing_main_red_first (t : T) : IO Unit := do
  t.fakes; twoHaiku t
  t.sw_ "t-comms" ["task", "add", "queued", "-p", "0"]
  t.sw_ "t-comms" ["queue", "add", "1"]
  t.sw_ "t-comms" ["task", "add", "main red: run 7", "-p", "3"]
  t.sw_ "t-comms" ["limits", "--queue-only", "on"]
  eq (← staffed t) (toJson 2)

def tests : List Case := [
  ("test_queue_add_appends_moves_and_places", test_queue_add_appends_moves_and_places),
  ("test_queue_rights", test_queue_rights),
  ("test_queue_left_on_done_and_drop", test_queue_left_on_done_and_drop),
  ("test_queue_says_why_not_startable", test_queue_says_why_not_startable),
  ("test_hold_and_claim", test_hold_and_claim),
  ("test_staffing_queue_beats_priority", test_staffing_queue_beats_priority),
  ("test_staffing_skips_held", test_staffing_skips_held),
  ("test_staffing_queue_only", test_staffing_queue_only),
  ("test_staffing_queue_only_off_is_priority", test_staffing_queue_only_off_is_priority),
  ("test_staffing_main_red_first", test_staffing_main_red_first)]

end SwarmLean.Tests.Cli.Queue

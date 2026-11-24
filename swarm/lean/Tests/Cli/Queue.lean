import Tests.Cli.Spawn

/-! Board #128, moved to Linear-style states: Ready is one ordered list (`swarm queue`, `queue add`/`rm` move a task's
place), `task backlog`/`ready` move a task between Backlog and Ready, `task assign` reserves one, `task drop
--duplicate-of` closes a Duplicate, and auto-spawn staffs Ready in its order (a main red task first). -/

namespace SwarmLean.Tests.Cli.Queue
open SwarmLean.Tests.Cli
open SwarmLean.Tests.Cli.Spawn (tick twoHaiku)
open Lean (Json toJson)

/-- Ready's ids in order, from the db: by place, then id. -/
def order (t : T) : IO (List Json) :=
  return (← t.q "select id from task where state='ready' order by qpos, id").toList.map (·.f "id")

/-- Backlog's ids in order. -/
def backlogOrder (t : T) : IO (List Json) :=
  return (← t.q "select id from task where state='backlog' order by qpos, id").toList.map (·.f "id")

def adds (t : T) (n : Nat) : IO Unit := for i in List.range n do t.sw_ "comms" ["task", "add", s!"t{i + 1}"]

def ids (l : List Nat) : List Json := l.map toJson

def test_queue_add_appends_moves_and_places (t : T) : IO Unit := do
  t.q_ "update swarm set comms='comms' where name='t'"
  has (← t.sw "comms" ["queue"]).stdout "(Ready empty)"
  adds t 4
  eq (← order t) (ids [1, 2, 3, 4])  -- a new task goes to the end of Ready
  has (← t.sw "comms" ["queue", "add", "3", "1"]).stdout "moved #3, #1"
  eq (← order t) (ids [2, 4, 3, 1])
  t.sw_ "comms" ["queue", "add", "4", "--front"]
  eq (← order t) (ids [4, 2, 3, 1])
  t.sw_ "comms" ["queue", "add", "1", "--before", "3"]
  eq (← order t) (ids [4, 2, 1, 3])
  t.sw_ "comms" ["queue", "add", "3", "--after", "4"]
  eq (← order t) (ids [4, 3, 2, 1])
  let out := (← t.sw "comms" ["queue"]).stdout
  has out "1. #4 startable  t4  [Medium]"
  has out "4. #1 startable  t1  [Medium]"
  has (← t.sw "comms" ["queue", "rm", "4"]).stdout "moved #4 to the end"
  eq (← order t) (ids [3, 2, 1, 4])
  has (← t.sw "comms" ["queue", "add", "9"] { ok := false }).stderr "no task #9"
  has (← t.sw "comms" ["queue", "add", "3", "--before", "3"] { ok := false }).stderr "#3 can't be placed next to itself"
  has (← t.sw "comms" ["board"]).stdout "t3  [Medium]  [queue 1]"
  has (← t.sw "comms" ["task", "show", "4"]).stdout "queue: 4"
  eq ((← t.q "select 1 x from event where kind='task-place' and data='#4 1 4'").size) 1

def test_queue_rights (t : T) : IO Unit := do
  t.q_ "update swarm set comms='comms' where name='t'"
  adds t 3
  t.sw_ "a" ["queue", "add", "1"]  -- any agent may move a task to the end
  eq (← order t) (ids [2, 3, 1])
  has (← t.sw "b" ["queue", "add", "3", "--front"] { ok := false }).stderr
    "only the communicator or the user can move a task other than to the end"
  t.sw_ "a" ["queue", "add", "1", "--front"] { env := [("SWARM_NAME", none)] }  -- the user (no SWARM_NAME)
  eq (← order t) (ids [1, 2, 3])

def test_queue_left_on_done_and_drop (t : T) : IO Unit := do
  t.q_ "update swarm set comms='comms' where name='t'"
  adds t 3
  t.sw_ "comms" ["task", "drop", "2"]
  eq (← order t) (ids [1, 3])
  eq ((← t.q1 "select qpos from task where id=2").f "qpos") Json.null  -- a closed task has no place
  t.sw_ "a" ["task", "claim", "1"]
  hasnt (← t.sw "comms" ["queue"]).stdout "#1"  -- In Progress: not in Ready
  t.sw_ "a" ["task", "done", "1", "--evidence", "abc"]
  eq (← order t) (ids [3])
  has (← t.sw "comms" ["queue"]).stdout "1. #3 startable"
  has (← t.sw "comms" ["queue", "add", "1"] { ok := false }).stderr
    "task #1 is Completed; only a Ready or Backlog task has a place"

def test_queue_says_why_not_startable (t : T) : IO Unit := do
  t.q_ "update swarm set comms='comms' where name='t'"
  adds t 4
  t.sw_ "comms" ["task", "after", "2", "1"]
  t.sw_ "comms" ["task", "backlog", "3", "--note", "needs the user's call"]
  t.sw_ "comms" ["task", "assign", "4", "human"]
  t.sw_ "comms" ["queue", "add", "2", "--front"]
  let out := (← t.sw "comms" ["queue"]).stdout
  has out "1. #2 waiting on #1  t2"
  has out "2. #1 startable  t1"
  has out "3. #4 assigned to human  t4"
  has out "Backlog: #3"

def test_backlog_and_claim (t : T) : IO Unit := do
  t.q_ "update swarm set comms='comms' where name='t'"
  adds t 1
  has (← t.sw "a" ["task", "backlog", "1", "--note", " "] { ok := false }).stderr "--note is empty"
  t.sw_ "a" ["task", "backlog", "1", "--note", "waits for the API"]  -- any agent may move a task to Backlog
  eq ((← t.q1 "select state, hold from task where id=1")) (json% {"state": "backlog", "hold": "waits for the API"})
  has (← t.sw "a" ["board"]).stdout "#1 Backlog"
  has (← t.sw "a" ["board"]).stdout "note: waits for the API"
  has (← t.sw "a" ["task", "show", "1"]).stdout "\nnote: waits for the API"
  has (← t.sw "a" ["task", "claim", "1"] { ok := false }).stderr "task #1 is in Backlog: waits for the API"
  has (← t.sw "a" ["task", "claim", "1", "--force"] { ok := false }).stderr "only the communicator or the user can --force it"
  t.sw_ "comms" ["task", "claim", "1", "--force"]
  eq ((← t.q1 "select owner, state from task where id=1")) (json% {"owner": "comms", "state": "in_progress"})
  has (← t.sw "comms" ["task", "ready", "1"] { ok := false }).stderr "task #1 is In Progress; only a Backlog task moves to Ready"
  has (← t.sw "comms" ["task", "backlog", "1", "--note", "x"] { ok := false }).stderr "(release it first)"

/-- Security review H1: only the communicator or the user moves a task from Backlog to Ready; each call, refused or
not, is an event with the caller's name and terminal. Backlog to Ready goes to the end of Ready. -/
def test_ready_rights (t : T) : IO Unit := do
  t.q_ "update swarm set comms='comms' where name='t'"
  adds t 3
  t.sw_ "a" ["task", "backlog", "1", "--note", "for the user"]
  eq (← backlogOrder t) (ids [1])
  let r ← t.sw "a" ["task", "ready", "1"] { ok := false, hc := some "w9" }
  has r.stderr "only the communicator (comms) or the user (human) can move #1 to Ready; you are a"
  eq ((← t.q1 "select count(*) n from event where kind='task-ready-refused' and agent='a' and data='#1 (terminal w9)'").f "n") 1
  has (← t.sw "comms" ["task", "ready", "1"] { hc := some "w1" }).stdout "#1 Ready, queue 3"
  eq (← order t) (ids [2, 3, 1])
  eq ((← t.q1 "select count(*) n from event where kind='task-ready' and agent='comms' and data='#1 (terminal w1)'").f "n") 1
  t.sw_ "a" ["task", "backlog", "2", "--note", "again"]
  t.sw_ "human" ["task", "ready", "2"]
  eq (← order t) (ids [3, 1, 2])
  has (← t.sw "comms" ["task", "ready", "2"] { ok := false }).stderr "task #2 is Ready; only a Backlog task moves to Ready"

/-- A Ready task can have an assignee before it starts: auto-spawn skips it and only its assignee claims it. -/
def test_assign (t : T) : IO Unit := do
  t.q_ "update swarm set comms='comms' where name='t'"
  adds t 2
  has (← t.sw "a" ["task", "assign", "1", "a"] { ok := false }).stderr "only the communicator (comms) or the user (human) can assign #1"
  has (← t.sw "comms" ["task", "assign", "1", "human"]).stdout "#1 assignee: human"
  eq ((← t.q1 "select state, owner from task where id=1")) (json% {"state": "ready", "owner": "human"})
  has (← t.sw "comms" ["board"]).stdout "#1 Ready       human  t1"
  let j := (Json.parse (← t.sw "comms" ["state", "--json", "--view", "board"]).stdout).toOption.getD .null
  let t1 : Json := match j.f "tasks" with | .arr a => (a.find? fun (x : Json) => x.f "id" == toJson 1).getD .null | _ => .null
  eq (t1.f "assignee", t1.f "owner", t1.f "category", t1.f "place") (json% "human", Json.null, json% "unstarted", json% 1)
  has (← t.sw "a" ["task", "claim", "1"] { ok := false }).stderr "task #1 is assigned to human; only it claims it"
  t.sw_ "human" ["task", "claim", "1"]
  eq ((← t.q1 "select state, owner from task where id=1")) (json% {"state": "in_progress", "owner": "human"})
  t.sw_ "comms" ["task", "assign", "2", "a"]
  t.sw_ "comms" ["task", "assign", "2", "--none"]
  eq ((← t.q1 "select owner from task where id=2").f "owner") Json.null
  has (← t.sw "comms" ["task", "assign", "2"] { ok := false }).stderr "usage: swarm task assign"
  has (← t.sw "comms" ["task", "assign", "1", "a"] { ok := false }).stderr "task #1 is In Progress; only a Ready or Backlog task is assigned"

/-- The old verbs and flags fail naming their replacement. -/
def test_old_verbs_name_their_replacement (t : T) : IO Unit := do
  t.q_ "update swarm set comms='comms' where name='t'"
  adds t 1
  has (← t.sw "comms" ["task", "hold", "1", "--why", "later"] { ok := false }).stderr "`swarm task backlog 1 --note"
  has (← t.sw "comms" ["task", "unhold", "1"] { ok := false }).stderr "`swarm task ready 1`"
  has (← t.sw "comms" ["task", "add", "x", "-p", "1"] { ok := false }).stderr
    "priorities are names now, not numbers: urgent (was 0), high (was 1), medium (was 2), low (was 3), or none"
  has (← t.sw "comms" ["task", "priority", "1", "0"] { ok := false }).stderr "priorities are names now"
  has (← t.sw "comms" ["limits", "--queue-only", "on"] { ok := false }).stderr "--queue-only is gone"
  has (← t.sw "comms" ["task", "priority", "1", "urgent"]).stdout "#1 Urgent"
  eq ((← t.q1 "select priority from task where id=1").f "priority") 1
  t.sw_ "comms" ["task", "priority", "1", "none"]
  has (← t.sw "comms" ["task", "show", "1"]).stdout "priority: No priority"

/-- The task the one auto-spawned agent took (room for one: two live, the number 2). -/
def staffed (t : T) : IO Json := do
  tick t 2
  let r ← t.q "select id from task where owner='t-2'"
  return if r.size == 1 then r[0]!.f "id" else .null

def test_staffing_ready_order_beats_priority (t : T) : IO Unit := do
  t.fakes; twoHaiku t
  t.sw_ "t-comms" ["task", "add", "urgent", "-p", "urgent"]
  t.sw_ "t-comms" ["task", "add", "later", "-p", "low"]
  t.sw_ "t-comms" ["queue", "add", "2", "--front"]
  eq (← staffed t) (toJson 2)

def test_staffing_is_ready_order (t : T) : IO Unit := do
  t.fakes; twoHaiku t
  t.sw_ "t-comms" ["task", "add", "low", "-p", "low"]
  t.sw_ "t-comms" ["task", "add", "high", "-p", "high"]
  eq (← staffed t) (toJson 1)  -- priority never reorders Ready

def test_staffing_skips_backlog_and_assigned (t : T) : IO Unit := do
  t.fakes; twoHaiku t
  t.sw_ "t-comms" ["task", "add", "one"]
  t.sw_ "t-comms" ["task", "add", "two"]
  t.sw_ "t-comms" ["task", "add", "three"]
  t.sw_ "t-comms" ["task", "backlog", "1", "--note", "later"]
  t.sw_ "t-comms" ["task", "assign", "2", "human"]
  eq (← staffed t) (toJson 3)

/-- A Cancelled dependency still blocks: staffing skips the task, it shows "waiting on #N (cancelled)", and it is a
needs-you item (remove the dependency or cancel it too); a Backlog task alone is not. -/
def test_cancelled_dep_blocks_and_needs_you (t : T) : IO Unit := do
  t.fakes; twoHaiku t
  t.sw_ "t-comms" ["task", "add", "dep"]
  t.sw_ "t-comms" ["task", "add", "work", "--after", "1"]
  t.sw_ "t-comms" ["task", "add", "parked"]
  t.sw_ "t-comms" ["task", "backlog", "3", "--note", "later"]
  has (← t.sw "t-comms" ["task", "drop", "1"]).stdout "#2 waits on #1"
  has (← t.sw "t-comms" ["queue"]).stdout "1. #2 waiting on #1 (cancelled)  work"
  has (← t.sw "t-comms" ["board"]).stdout "waiting on #1 (cancelled)"
  eq (← staffed t) Json.null
  let s := (Json.parse (← t.sw "t-comms" ["state", "--json", "--view", "summary"]).stdout).toOption.getD .null
  let needs := match s.f "needs" with | .arr a => a.toList.filter fun (x : Json) => x.f "kind" == json% "dep-cancelled" | _ => []
  eq (toJson needs) (json% [{"kind": "dep-cancelled", "task": 2, "title": "work", "deps": [1]}])
  t.sw_ "t-comms" ["task", "after", "2"]  -- remove the dependency
  eq (← staffed t) (toJson 2)

def test_staffing_main_red_first (t : T) : IO Unit := do
  t.fakes; twoHaiku t
  t.sw_ "t-comms" ["task", "add", "queued", "-p", "urgent"]
  t.sw_ "t-comms" ["task", "add", "main red: run 7", "-p", "low"]
  eq (← staffed t) (toJson 2)

/-- A person's claim has no expiring lease: watchd never frees it, whatever its lease column says (the user has no
agent row, so no ended or hung holder). -/
def test_human_claim_never_freed (t : T) : IO Unit := do
  t.q_ "update swarm set comms='comms' where name='t'"
  adds t 1
  t.sw_ "human" ["task", "claim", "1"]
  t.q_ "update task set lease_until=1 where id=1"
  for _ in [0, 1] do t.sw_ "a" ["watchd", "--once", "--comms", "comms", "--max-agents", "0"]
  eq (← t.q1 "select state, owner from task where id=1") (json% {"state": "in_progress", "owner": "human"})
  eq ((← t.q "select 1 x from msg where body like '%#1%lease%'").size) 0
  hasnt (← t.sw "comms" ["board"]).stdout "lease"

def test_duplicate (t : T) : IO Unit := do
  t.q_ "update swarm set comms='comms' where name='t'"
  adds t 2
  has (← t.sw "comms" ["task", "drop", "2", "--duplicate-of", "2"] { ok := false }).stderr "#2 can't be a duplicate of itself"
  has (← t.sw "comms" ["task", "drop", "2", "--duplicate-of", "9"] { ok := false }).stderr "no task #9 to be a duplicate of"
  has (← t.sw "comms" ["task", "drop", "2", "--duplicate-of", "1", "--note", "same ask"]).stdout "#2 Duplicate of #1"
  eq (← t.q1 "select state, dup_of, hold, qpos from task where id=2")
    (json% {"state": "duplicate", "dup_of": 1, "hold": "same ask"})
  has (← t.sw "comms" ["task", "show", "2"]).stdout "duplicate of #1"
  eq ((← t.q1 "select count(*) n from event where kind='task-duplicate' and data='#2 #1'").f "n") 1
  has (← t.sw "comms" ["task", "drop", "1"]).stdout "#1 Cancelled"

def tests : List Case := [
  ("test_queue_add_appends_moves_and_places", test_queue_add_appends_moves_and_places),
  ("test_queue_rights", test_queue_rights),
  ("test_queue_left_on_done_and_drop", test_queue_left_on_done_and_drop),
  ("test_queue_says_why_not_startable", test_queue_says_why_not_startable),
  ("test_backlog_and_claim", test_backlog_and_claim),
  ("test_ready_rights", test_ready_rights),
  ("test_assign", test_assign),
  ("test_old_verbs_name_their_replacement", test_old_verbs_name_their_replacement),
  ("test_staffing_ready_order_beats_priority", test_staffing_ready_order_beats_priority),
  ("test_staffing_is_ready_order", test_staffing_is_ready_order),
  ("test_staffing_skips_backlog_and_assigned", test_staffing_skips_backlog_and_assigned),
  ("test_cancelled_dep_blocks_and_needs_you", test_cancelled_dep_blocks_and_needs_you),
  ("test_staffing_main_red_first", test_staffing_main_red_first),
  ("test_human_claim_never_freed", test_human_claim_never_freed),
  ("test_duplicate", test_duplicate)]

end SwarmLean.Tests.Cli.Queue

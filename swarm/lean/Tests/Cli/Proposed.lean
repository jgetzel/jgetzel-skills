import Tests.Cli.Queue

/-! A task an agent adds is Proposed (board #1983, ll #1979): it waits for the communicator's triage, and queue, the pool a
free agent is offered, auto-spawn and `task claim` skip it as they skip Backlog. The communicator's, the user's and CI's
tasks are Ready as before (CI's: watchd_run_spec's red-main cases). `task ready`, `task backlog`, `task drop`
(`--duplicate-of`) and `task edit --append` move or fold it. -/

namespace SwarmLean.Tests.Cli.Proposed
open SwarmLean.Tests.Cli
open SwarmLean.Tests.Cli.Spawn (tick twoHaiku)
open SwarmLean.Tests.Cli.Queue (staffed)
open Lean (Json toJson)

/-- The states of every task, by id. -/
def states (t : T) : IO (List Json) :=
  return (← t.q "select state from task order by id").toList.map (·.f "state")

def names (l : List String) : List Json := l.map toJson

def test_add_by_who_decides_state (t : T) : IO Unit := do
  t.q_ "update swarm set comms='comms' where name='t'"
  let r ← t.sw "a" ["task", "add", "an agent's find"] { proposes := true }
  has r.stdout "task #1"
  has r.stdout "Proposed: staffing and `swarm queue` skip it until the communicator or the user runs `swarm task ready 1`"
  let r ← t.sw "comms" ["task", "add", "the communicator's"] { proposes := true }
  hasnt r.stdout "Proposed"
  t.sw_ "human" ["task", "add", "the user's"] { proposes := true }
  eq (← states t) (names ["proposed", "ready", "ready"])
  eq ((← t.q "select 1 x from event where kind='task-add' and data like '#1 %'").size) 1

def test_queue_and_board_show_proposed_apart (t : T) : IO Unit := do
  t.q_ "update swarm set comms='comms' where name='t'"
  t.sw_ "comms" ["task", "add", "ready one"] { proposes := true }
  t.sw_ "a" ["task", "add", "found two"] { proposes := true }
  t.sw_ "b" ["task", "add", "found three"] { proposes := true }
  t.sw_ "comms" ["task", "add", "parked"] { proposes := true }
  t.sw_ "comms" ["task", "backlog", "4", "--note", "later"]
  let q := (← t.sw "comms" ["queue"]).stdout
  has q "1. #1 startable  ready one"
  has q "Backlog: #4"
  has q "Proposed: #2, #3"
  hasnt q "#2 startable"
  let b := (← t.sw "comms" ["board"]).stdout
  has b "Proposed: 2 (not staffed until the communicator or the user runs `swarm task ready <id>`)"
  has b "#2 Proposed"
  has b "found three  [Medium]  [proposed 2]"
  has b "#1 Ready"
  has b "#4 Backlog"
  has (← t.sw "comms" ["task", "show", "3"]).stdout "proposed: 2"
  let j := (Json.parse (← t.sw "comms" ["board", "--json"]).stdout).toOption.getD .null
  eq ((j.f "counts").f "proposed") (toJson 2)
  eq (((j.f "categories").f "unstarted")) (toJson 3)  -- Proposed is Unstarted beside Ready
  let k := match j.f "tasks" with | .arr a => a.toList.filter fun (x : Json) => x.f "id" == toJson 3 | _ => []
  eq (toJson (k.map fun x => [x.f "state", x.f "category", x.f "place"])) (json% [["proposed", "unstarted", 2]])

def test_proposed_is_not_staffed_or_claimed_until_ready (t : T) : IO Unit := do
  t.fakes; twoHaiku t
  t.sw_ "t-comms" ["task", "add", "unfiled"] { proposes := true }
  t.sw_ "t-comms" ["task", "backlog", "1", "--note", "x"]
  t.sw_ "a" ["task", "add", "found"] { proposes := true }
  eq (← staffed t) Json.null  -- auto-spawn never starts it
  has (← t.sw "a" ["task", "claim", "2"] { ok := false }).stderr
    "task #2 is Proposed, waiting for triage; the communicator or the user runs `swarm task ready` on it first (or the communicator's --force)"
  has (← t.sw "a" ["task", "claim", "2", "--force"] { ok := false }).stderr "only the communicator or the user can --force it"
  has (← t.sw "a" ["task", "ready", "2"] { ok := false }).stderr "only the communicator"
  has (← t.sw "t-comms" ["task", "claim", "2"] { ok := false }).stderr "task #2 is Proposed"
  eq (← states t) (names ["backlog", "proposed"])
  has (← t.sw "t-comms" ["task", "ready", "2"]).stdout "#2 Ready, queue 1"
  eq (← staffed t) (toJson 2)  -- Ready: the next tick staffs it

def test_comms_force_claims_a_proposed_task (t : T) : IO Unit := do
  t.q_ "update swarm set comms='comms' where name='t'"
  t.sw_ "a" ["task", "add", "found"] { proposes := true }
  has (← t.sw "comms" ["task", "claim", "1", "--force"]).stdout "claimed #1"
  eq (← t.q1 "select state, owner from task where id=1") (json% {"state": "in_progress", "owner": "comms"})

def test_ready_to_end_and_other_moves (t : T) : IO Unit := do
  t.q_ "update swarm set comms='comms' where name='t'"
  t.sw_ "comms" ["task", "add", "r1"] { proposes := true }
  for n in ["p2", "p3", "p4", "p5", "p6"] do t.sw_ "a" ["task", "add", n] { proposes := true }
  t.sw_ "comms" ["task", "add", "r7"] { proposes := true }
  t.sw_ "comms" ["task", "ready", "4"]  -- to the end of Ready, after r7
  eq ((← t.q "select id from task where state='ready' order by qpos, id").toList.map (·.f "id")) [toJson 1, toJson 7, toJson 4]
  has (← t.sw "comms" ["task", "ready", "4"] { ok := false }).stderr "task #4 is Ready; only a Backlog or Proposed task moves to Ready"
  t.sw_ "comms" ["task", "backlog", "2", "--note", "waits for the API"]  -- Backlog, with the note
  eq (← t.q1 "select state, hold from task where id=2") (json% {"state": "backlog", "hold": "waits for the API"})
  has (← t.sw "comms" ["task", "drop", "3", "--duplicate-of", "1", "--note", "same ask"]).stdout "#3 Duplicate of #1"
  has (← t.sw "comms" ["task", "drop", "5"]).stdout "#5 Cancelled"
  t.sw_ "b" ["task", "edit", "6", "--append", "more detail from the second find"]  -- fold a finding into a proposal
  eq (← t.q1 "select state from task where id=6") (json% {"state": "proposed"})
  has (← t.sw "comms" ["task", "show", "6"]).stdout "more detail from the second find"
  eq (← states t) (names ["ready", "backlog", "duplicate", "ready", "cancelled", "proposed", "ready"])
  -- a place move and an assignment keep it Proposed
  t.sw_ "a" ["task", "add", "p8"] { proposes := true }
  t.sw_ "comms" ["task", "assign", "8", "human"]
  eq (← t.q1 "select state, owner from task where id=8") (json% {"state": "proposed", "owner": "human"})
  t.sw_ "comms" ["queue", "add", "8", "--before", "6"]
  eq (← t.q1 "select state from task where id=8") (json% {"state": "proposed"})

def tests : List Case := [
  ("test_add_by_who_decides_state", test_add_by_who_decides_state),
  ("test_queue_and_board_show_proposed_apart", test_queue_and_board_show_proposed_apart),
  ("test_proposed_is_not_staffed_or_claimed_until_ready", test_proposed_is_not_staffed_or_claimed_until_ready),
  ("test_comms_force_claims_a_proposed_task", test_comms_force_claims_a_proposed_task),
  ("test_ready_to_end_and_other_moves", test_ready_to_end_and_other_moves)]

end SwarmLean.Tests.Cli.Proposed

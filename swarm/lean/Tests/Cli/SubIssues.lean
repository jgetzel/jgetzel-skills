import Tests.Cli.Spawn

/-! Sub-issues (board: a goal hierarchy, column task.parent): setting and clearing a parent, its refusals, show and
board output, the v3 migration, a container never staffed, progress over the leaves, the sub-issues-done need and
closing a task that has open sub-issues. -/

namespace SwarmLean.Tests.Cli.SubIssues
open SwarmLean.Tests.Cli
open SwarmLean.Tests.Cli.Spawn (tick twoHaiku)
open Lean (Json toJson)

/-- Comms is the communicator and n tasks t1..tn are added. -/
def setup (t : T) (n : Nat) : IO Unit := do
  t.q_ "update swarm set comms='comms' where name='t'"
  for i in List.range n do t.sw_ "comms" ["task", "add", s!"t{i + 1}"]

def parse (s : String) : IO Json := match Json.parse s with
  | .ok j => pure j
  | .error e => fail s!"not JSON ({e}): {s}"

/-- `task show --json` of task n. -/
def showJ (t : T) (n : Nat) : IO Json := do parse (← t.sw "comms" ["task", "show", toString n, "--json"]).stdout

/-- Task n claimed by a and done: Completed. -/
def finish (t : T) (n : Nat) : IO Unit := do
  t.sw_ "a" ["task", "claim", toString n]
  t.sw_ "a" ["task", "done", toString n, "--evidence", "x"]

def stateOf (t : T) (n : Nat) : IO Json := return (← t.q1 "select state from task where id=?" [.int n]).f "state"

def parentOf (t : T) (n : Nat) : IO Json := return (← t.q1 "select parent from task where id=?" [.int n]).f "parent"

def refuse (t : T) (args : List String) (want : String) : IO Unit :=
  do has (← t.sw "comms" args { ok := false }).stderr want

def arr : Json → List Json | .arr a => a.toList | _ => []

/-- The needs of a state of kind sub-issues-done. -/
def subNeeds (s : Json) : List Json := (arr (s.f "needs")).filter fun x => x.f "kind" == json% "sub-issues-done"

/-- The summary view's sub-issues-done needs. -/
def summaryNeeds (t : T) : IO (List Json) :=
  return subNeeds (← parse (← t.sw "a" ["state", "--json", "--view", "summary"]).stdout)

/-- The swarms view's swarm t. -/
def swarmT (t : T) : IO Json := do
  let s ← parse (← t.sw "a" ["state", "--json", "--view", "swarms"]).stdout
  return (arr (s.f "swarms")).find? (fun x => x.f "name" == json% "t") |>.getD .null

def test_sub_parent_set_clear_and_show (t : T) : IO Unit := do
  setup t 3
  has (← t.sw "comms" ["task", "parent", "2", "1"]).stdout "#2 parent: #1"
  eq (← parentOf t 2) (toJson 1)
  t.sw_ "comms" ["task", "parent", "3", "2"]
  let txt1 := (← t.sw "comms" ["task", "show", "1"]).stdout
  has txt1 "Sub-issues: 0/1 done"
  has txt1 "  #2 Ready t2"
  let txt2 := (← t.sw "comms" ["task", "show", "2"]).stdout
  has txt2 "Parent: #1 t1 (Ready)"
  has txt2 "Sub-issues: 0/1 done"
  hasnt (← t.sw "comms" ["task", "show", "1"]).stdout "Parent:"
  let j3 ← showJ t 3
  eq (j3.f "parent") (json% 2)
  eq (j3.f "parent_title") (json% "t2")
  eq (j3.f "ancestors") (json% [{"id": 1, "title": "t1", "state": "ready"}, {"id": 2, "title": "t2", "state": "ready"}])
  eq (j3.f "sub_issues") (json% [])
  eq (j3.f "progress") Json.null
  let j1 ← showJ t 1
  eq (j1.f "parent") Json.null
  eq (j1.f "ancestors") (json% [])
  eq (j1.f "sub_issues") (json% [{"id": 2, "title": "t2", "state": "ready", "owner": null}])
  eq (j1.f "progress") (json% {"done": 0, "total": 1})
  -- clear
  has (← t.sw "comms" ["task", "parent", "3", "--none"]).stdout "#3 parent: none"
  eq (← parentOf t 3) Json.null
  eq ((← showJ t 3).f "ancestors") (json% [])
  eq ((← showJ t 2).f "progress") Json.null
  -- re-parenting moves it
  t.sw_ "comms" ["task", "parent", "2", "3"]
  eq (← parentOf t 2) (toJson 3)
  eq ((← showJ t 1).f "progress") Json.null
  -- the board's tree
  t.sw_ "comms" ["task", "parent", "3", "1"]
  let b := (← t.sw "comms" ["board", "--by", "parent"]).stdout
  has b "#1 Ready"
  has b "  [0/1 done]"
  has b "
  #3 Ready"
  has b "
    #2 Ready"
  has (← t.sw "comms" ["task", "parent", "2"] { ok := false }).stderr "usage: swarm task parent"

def test_sub_parent_refusals (t : T) : IO Unit := do
  setup t 3
  refuse t ["task", "parent", "1", "1"] "task #1 can't be its own parent"
  t.sw_ "comms" ["task", "parent", "2", "1"]
  t.sw_ "comms" ["task", "parent", "3", "2"]
  refuse t ["task", "parent", "1", "3"] "that would be a cycle"
  refuse t ["task", "parent", "1", "2"] "that would be a cycle"
  eq (← parentOf t 1) Json.null
  refuse t ["task", "parent", "9", "1"] "no task #9"
  refuse t ["task", "parent", "1", "9"] "no task #9"
  t.sw_ "comms" ["task", "add", "t4"]
  t.sw_ "comms" ["task", "add", "t5"]
  finish t 4
  t.sw_ "comms" ["task", "drop", "5"]
  refuse t ["task", "parent", "1", "4"] "task #4 is Completed; a closed task can't take a new sub-issue"
  refuse t ["task", "parent", "1", "5"] "task #5 is Cancelled; a closed task can't take a new sub-issue"
  eq (← parentOf t 1) Json.null
  -- task add --parent: the same refusals, and no task is filed
  refuse t ["task", "add", "x", "--parent", "9"] "no task #9"
  refuse t ["task", "add", "x", "--parent", "4"] "can't take a new sub-issue"
  refuse t ["task", "add", "x", "--parent", "5"] "can't take a new sub-issue"
  eq ((← t.q "select id from task")).size 5

def test_sub_add_with_parent (t : T) : IO Unit := do
  setup t 1
  has (← t.sw "comms" ["task", "add", "kid", "--parent", "1"]).stdout "task #2"
  let j ← showJ t 2
  eq (j.f "parent") (json% 1)
  eq (j.f "parent_title") (json% "t1")
  eq (← parentOf t 2) (toJson 1)
  eq ((← showJ t 1).f "sub_issues") (json% [{"id": 2, "title": "kid", "state": "ready", "owner": null}])
  eq ((← showJ t 1).f "progress") (json% {"done": 0, "total": 1})

def test_sub_migration_v2 (t : T) : IO Unit := do
  -- the fixture's db, taken back to version 2: no parent column, no index
  let c ← Sqlite.Conn.open t.db false
  discard <| c.exec "drop index if exists task_parent"
  discard <| c.exec "alter table task drop column parent"
  discard <| c.exec "insert into task(id, title, state, owner) values(7, 'old', 'ready', null)"
  discard <| c.exec "pragma user_version=2"
  let cols ← c.query "select count(*) from pragma_table_info('task') where name='parent'"
  eq (cols[0]?.bind (·[0]?) == some (.int 0)) true "the v2 db has no parent column"
  has (← t.sw "comms" ["board"]).stdout "#7"
  eq ((← t.q1 "select count(*) n from pragma_table_info('task') where name='parent'").f "n") 1
  eq (← t.q1 "select id, title, state, parent from task where id=7") (json% {"id": 7, "title": "old", "state": "ready"})
  eq ((← t.q1 "select user_version from pragma_user_version").f "user_version") 4
  eq ((← t.q1 "select count(*) n from swarm where name='t'").f "n") 1
  eq ((← t.q1 "select count(*) n from sqlite_master where name='task_parent'").f "n") 1
  -- and a parent can be set on the migrated row
  t.sw_ "comms" ["task", "add", "new"]
  t.sw_ "comms" ["task", "parent", "7", "8"]
  eq (← parentOf t 7) (toJson 8)

def staffed (t : T) : IO Json := do
  tick t 2
  let r ← t.q "select id from task where owner='t-2'"
  return if r.size == 1 then r[0]!.f "id" else .null

def test_sub_container_is_not_staffed (t : T) : IO Unit := do
  t.fakes; twoHaiku t
  t.sw_ "t-comms" ["task", "add", "parent"]
  t.sw_ "t-comms" ["task", "add", "kid", "--parent", "1"]
  let q := (← t.sw "t-comms" ["queue"]).stdout
  has q "1. #1 has open sub-issues  parent"
  has q "2. #2 startable  kid"
  eq (← staffed t) (toJson 2)

def test_sub_backlog_child_still_blocks_parent (t : T) : IO Unit := do
  t.fakes; twoHaiku t
  t.sw_ "t-comms" ["task", "add", "parent"]
  t.sw_ "t-comms" ["task", "add", "kid", "--parent", "1"]
  t.sw_ "t-comms" ["task", "backlog", "2", "--note", "later"]
  has (← t.sw "t-comms" ["queue"]).stdout "1. #1 has open sub-issues  parent"
  eq (← staffed t) Json.null

def test_sub_parent_startable_when_children_closed (t : T) : IO Unit := do
  t.fakes; twoHaiku t
  t.sw_ "t-comms" ["task", "add", "parent"]
  t.sw_ "t-comms" ["task", "add", "kid", "--parent", "1"]
  t.sw_ "t-comms" ["task", "add", "kid2", "--parent", "1"]
  t.sw_ "t-comms" ["task", "drop", "2"]
  has (← t.sw "t-comms" ["queue"]).stdout "has open sub-issues"
  t.sw_ "t-comms" ["task", "drop", "3"]
  let q := (← t.sw "t-comms" ["queue"]).stdout
  has q "1. #1 startable  parent"
  eq (← staffed t) (toJson 1)

def test_sub_swarms_view_next_skips_container (t : T) : IO Unit := do
  setup t 0
  t.sw_ "comms" ["task", "add", "parent"]
  t.sw_ "comms" ["task", "add", "kid", "--parent", "1"]
  let s ← swarmT t
  eq ((arr (s.f "next")).map (·.f "id")) [json% 2]
  eq (s.f "ready") (json% 1)
  t.sw_ "comms" ["task", "drop", "2"]
  let s ← swarmT t
  eq ((arr (s.f "next")).map (·.f "id")) [json% 1]
  eq (s.f "ready") (json% 1)

def test_sub_progress_nested (t : T) : IO Unit := do
  setup t 1
  for (title, p) in [("c", 1), ("g1", 2), ("g2", 2), ("leaf", 1)] do
    t.sw_ "comms" ["task", "add", title, "--parent", toString p]
  -- 1 -> [2 -> [3, 4], 5]
  eq ((← showJ t 1).f "progress") (json% {"done": 0, "total": 3})
  eq ((← showJ t 2).f "progress") (json% {"done": 0, "total": 2})
  eq ((← showJ t 3).f "progress") Json.null
  eq ((← showJ t 5).f "progress") Json.null
  finish t 3
  eq ((← showJ t 1).f "progress") (json% {"done": 1, "total": 3})
  eq ((← showJ t 2).f "progress") (json% {"done": 1, "total": 2})
  t.sw_ "comms" ["task", "drop", "4"]  -- a cancelled leaf leaves the total
  eq ((← showJ t 1).f "progress") (json% {"done": 1, "total": 2})
  eq ((← showJ t 2).f "progress") (json% {"done": 1, "total": 1})
  eq ((← showJ t 1).f "sub_issues").len 2
  has (← t.sw "comms" ["task", "show", "1"]).stdout "Sub-issues: 1/2 done"
  has (← t.sw "comms" ["board", "--by", "parent", "--all"]).stdout "[1/2 done]"
  -- state --json (full view): parent and progress on every task
  let s ← parse (← t.sw "a" ["state", "--json"]).stdout
  let tk (n : Nat) := (arr (s.f "tasks")).find? (fun x => x.f "id" == toJson n) |>.getD .null
  eq ((tk 1).f "parent", (tk 1).f "progress") (json% [null, {"done": 1, "total": 2}])
  eq ((tk 2).f "parent", (tk 2).f "progress") (json% [1, {"done": 1, "total": 1}])
  eq ((tk 3).f "parent", (tk 3).f "progress") (json% [2, null])
  eq ((tk 5).f "parent", (tk 5).f "progress") (json% [1, null])

def test_sub_needs_when_last_descendant_closes (t : T) : IO Unit := do
  setup t 1
  t.sw_ "comms" ["task", "add", "k1", "--parent", "1"]
  t.sw_ "comms" ["task", "add", "k2", "--parent", "2"]
  eq (← summaryNeeds t) (json% [])
  eq (subNeeds (← swarmT t)) (json% [])
  finish t 3  -- the grandchild: k1 now has all its sub-issues done, and the root has k1 open
  let want (task : Nat) (title : String) (d tot : Nat) : Json :=
    json% {"kind": "sub-issues-done", "task": $task, "title": $title, "progress": {"done": $d, "total": $tot}}
  eq (← summaryNeeds t) [want 2 "k1" 1 1]
  eq (subNeeds (← swarmT t)) [want 2 "k1" 1 1]
  let ms ← parse (← t.sw "a" ["state", "--json", "--view", "swarms"]).stdout
  eq (subNeeds ms) [want 2 "k1" 1 1]
  finish t 2
  eq (← summaryNeeds t) [want 1 "t1" 1 1]
  eq (subNeeds (← swarmT t)) [want 1 "t1" 1 1]
  finish t 1  -- completing the parent ends the need
  eq (← summaryNeeds t) (json% [])
  eq (subNeeds (← swarmT t)) (json% [])

def test_sub_needs_gone_when_parent_cancelled (t : T) : IO Unit := do
  setup t 1
  t.sw_ "comms" ["task", "add", "k1", "--parent", "1"]
  t.sw_ "comms" ["task", "add", "k2", "--parent", "1"]
  finish t 2
  eq (← summaryNeeds t).length 0
  t.sw_ "comms" ["task", "drop", "3"]  -- the last open one cancelled: the rest is done
  eq (← summaryNeeds t).length 1
  eq (← stateOf t 1) (json% "ready")  -- a parent is never completed on its own
  t.sw_ "comms" ["task", "drop", "1"]
  eq (← summaryNeeds t) (json% [])
  eq (subNeeds (← swarmT t)) (json% [])

def seed (t : T) : IO Unit := do
  -- 1 -> [2 -> [3, 4], 5]
  setup t 1
  for (title, p) in [("c", 1), ("g1", 2), ("g2", 2), ("leaf", 1)] do
    t.sw_ "comms" ["task", "add", title, "--parent", toString p]

def test_sub_done_refuses_with_open_sub_issues (t : T) : IO Unit := do
  seed t
  t.sw_ "a" ["task", "claim", "1"]
  let r ← t.sw "a" ["task", "done", "1", "--evidence", "x"] { ok := false }
  has r.stderr "#1 has 4 open sub-issues"
  has r.stderr "--children"
  eq (← stateOf t 1) (json% "in_progress")
  eq ((← t.q "select id from task where state='ready'")).size 4
  has (← t.sw "a" ["task", "done", "1", "--evidence", "x", "--children", "bogus"] { ok := false }).stderr "must be one of "
  eq (← stateOf t 1) (json% "in_progress")

def test_sub_done_children_cancel (t : T) : IO Unit := do
  seed t
  finish t 3
  t.sw_ "a" ["task", "claim", "1"]
  t.sw_ "a" ["task", "done", "1", "--evidence", "x", "--children", "cancel"]
  eq (← stateOf t 1) (json% "completed")
  eq (← stateOf t 2) (json% "cancelled")  -- below the root at depth 1 and still open
  eq (← stateOf t 3) (json% "completed")  -- done stays done
  eq (← stateOf t 4) (json% "cancelled")
  eq (← stateOf t 5) (json% "cancelled")
  eq ((← t.q "select id from task where state='ready' or state='in_progress'")).size 0
  eq (← parentOf t 4) (toJson 2)

def test_sub_done_children_keep (t : T) : IO Unit := do
  seed t
  t.sw_ "a" ["task", "claim", "1"]
  t.sw_ "a" ["task", "done", "1", "--evidence", "x", "--children", "keep"]
  eq (← stateOf t 1) (json% "completed")
  for n in [2, 3, 4, 5] do eq (← stateOf t n) (json% "ready")
  eq (← parentOf t 2) (toJson 1)
  eq (← parentOf t 3) (toJson 2)
  eq (← parentOf t 5) (toJson 1)
  -- a closed parent with open children is no container's need
  eq (← summaryNeeds t) (json% [])

def test_sub_drop_with_open_sub_issues (t : T) : IO Unit := do
  seed t
  let r ← t.sw "comms" ["task", "drop", "2"] { ok := false }
  has r.stderr "#2 has 2 open sub-issues"
  has r.stderr "--children"
  eq (← stateOf t 2) (json% "ready")
  let r ← t.sw "comms" ["task", "drop", "1"] { ok := false }
  has r.stderr "#1 has 4 open sub-issues"
  -- keep: the parent is cancelled, the children stay open under it
  t.sw_ "comms" ["task", "drop", "2", "--children", "keep"]
  eq (← stateOf t 2) (json% "cancelled")
  for n in [3, 4] do
    eq (← stateOf t n) (json% "ready")
    eq (← parentOf t n) (toJson 2)
  -- cancel: every open descendant goes too
  t.sw_ "comms" ["task", "drop", "1", "--children", "cancel"]
  for n in [1, 3, 4, 5] do eq (← stateOf t n) (json% "cancelled")
  eq ((← t.q "select id from task where state='ready'")).size 0

def test_sub_user_closes_unclaimed_container (t : T) : IO Unit := do
  setup t 0
  for (title, p) in [("parent", none), ("kid", some 1), ("other", none)] do
    t.sw_ "comms" (["task", "add", title] ++ match p with | some n => ["--parent", toString n] | none => [])
  finish t 2
  -- an agent still needs the claim; so does a task with no sub-issues, for the user too
  has (← t.sw "a" ["task", "done", "1", "--evidence", "x"] { ok := false }).stderr "is not claimed by you"
  has (← t.sw "human" ["task", "done", "3", "--evidence", "x"] { ok := false }).stderr "is not claimed by you"
  eq (← stateOf t 1) (json% "ready")
  has (← t.sw "human" ["task", "done", "1", "--evidence", ""] { ok := false }).stderr "--evidence is empty"
  -- the user closes the parent whose sub-issues are done, with no claim
  t.sw_ "human" ["task", "done", "1", "--evidence", "all sub-issues done"]
  eq (← stateOf t 1) (json% "completed")
  eq ((← t.q1 "select evidence from task where id=1").f "evidence") (json% "all sub-issues done")
  eq (← summaryNeeds t) (json% [])
  eq (← stateOf t 3) (json% "ready")

def test_sub_comms_closes_backlog_container_with_open_kids (t : T) : IO Unit := do
  seed t
  t.sw_ "comms" ["task", "backlog", "1", "--note", "later"]
  -- the open sub-issues still need --children; the communicator then closes with no claim
  has (← t.sw "comms" ["task", "done", "1", "--evidence", "x"] { ok := false }).stderr "#1 has 4 open sub-issues"
  eq (← stateOf t 1) (json% "backlog")
  has (← t.sw "a" ["task", "done", "1", "--evidence", "x", "--children", "cancel"] { ok := false }).stderr "is not claimed by you"
  t.sw_ "comms" ["task", "done", "1", "--evidence", "x", "--children", "cancel"]
  eq (← stateOf t 1) (json% "completed")
  for n in [2, 3, 4, 5] do eq (← stateOf t n) (json% "cancelled")

def test_sub_swarms_view_tasks_carry_provenance_parents (t : T) : IO Unit := do
  setup t 1
  t.sw_ "a" ["task", "claim", "1"]
  t.sw_ "a" ["task", "add", "filed"]
  let s ← parse (← t.sw "a" ["state", "--json", "--view", "swarms"]).stdout
  let task (n : Nat) := (arr (s.f "tasks")).find? (·.f "id" == toJson n) |>.getD .null
  eq ((task 2).f "parents") (json% [1])
  eq ((task 1).f "parents") (json% [])

def test_sub_grandparent_not_staffed_over_kept_grandchild (t : T) : IO Unit := do
  t.fakes; twoHaiku t
  t.sw_ "t-comms" ["task", "add", "grand"]
  t.sw_ "t-comms" ["task", "add", "mid", "--parent", "1"]
  t.sw_ "t-comms" ["task", "add", "leaf", "--parent", "2"]
  t.sw_ "t-comms" ["task", "drop", "2", "--children", "keep"]
  let q := (← t.sw "t-comms" ["queue"]).stdout
  has q "#1 has open sub-issues  grand"
  has q "#3 startable  leaf"
  eq (← staffed t) (toJson 3)

def test_sub_refuses_waiting_on_an_ancestor (t : T) : IO Unit := do
  setup t 4
  t.sw_ "comms" ["task", "parent", "3", "2"]
  t.sw_ "comms" ["task", "parent", "2", "1"]
  -- adding a dep from a sub-issue on its parent or a higher ancestor
  refuse t ["task", "after", "3", "2"] "#3 is a sub-issue of #2"
  refuse t ["task", "after", "3", "1"] "#3 is a sub-issue of #1"
  refuse t ["task", "after", "2", "4,1"] "#2 is a sub-issue of #1"
  t.sw_ "comms" ["task", "after", "1", "2"]
  t.sw_ "comms" ["task", "after", "3", "4"]
  -- a task that waits on N or an ancestor of N can't become N's sub-issue
  t.sw_ "comms" ["task", "after", "4", "1"]
  refuse t ["task", "parent", "4", "3"] "#4 is a sub-issue of #1"
  refuse t ["task", "parent", "4", "2"] "#4 is a sub-issue of #1"
  eq (← parentOf t 4) Json.null
  -- task add --parent with --after on the parent or an ancestor
  refuse t ["task", "add", "k", "--parent", "3", "--after", "2"] "is a sub-issue of #2"
  refuse t ["task", "add", "k", "--parent", "3", "--after", "3"] "is a sub-issue of #3"
  t.sw_ "comms" ["task", "add", "k", "--parent", "3", "--after", "4"]
  eq (← parentOf t 5) (toJson 3)

def tests : List Case := [
  ("test_sub_parent_set_clear_and_show", test_sub_parent_set_clear_and_show),
  ("test_sub_parent_refusals", test_sub_parent_refusals),
  ("test_sub_add_with_parent", test_sub_add_with_parent),
  ("test_sub_migration_v2", test_sub_migration_v2),
  ("test_sub_container_is_not_staffed", test_sub_container_is_not_staffed),
  ("test_sub_backlog_child_still_blocks_parent", test_sub_backlog_child_still_blocks_parent),
  ("test_sub_parent_startable_when_children_closed", test_sub_parent_startable_when_children_closed),
  ("test_sub_swarms_view_next_skips_container", test_sub_swarms_view_next_skips_container),
  ("test_sub_grandparent_not_staffed_over_kept_grandchild", test_sub_grandparent_not_staffed_over_kept_grandchild),
  ("test_sub_refuses_waiting_on_an_ancestor", test_sub_refuses_waiting_on_an_ancestor),
  ("test_sub_progress_nested", test_sub_progress_nested),
  ("test_sub_needs_when_last_descendant_closes", test_sub_needs_when_last_descendant_closes),
  ("test_sub_needs_gone_when_parent_cancelled", test_sub_needs_gone_when_parent_cancelled),
  ("test_sub_done_refuses_with_open_sub_issues", test_sub_done_refuses_with_open_sub_issues),
  ("test_sub_done_children_cancel", test_sub_done_children_cancel),
  ("test_sub_done_children_keep", test_sub_done_children_keep),
  ("test_sub_drop_with_open_sub_issues", test_sub_drop_with_open_sub_issues),
  ("test_sub_user_closes_unclaimed_container", test_sub_user_closes_unclaimed_container),
  ("test_sub_comms_closes_backlog_container_with_open_kids", test_sub_comms_closes_backlog_container_with_open_kids),
  ("test_sub_swarms_view_tasks_carry_provenance_parents", test_sub_swarms_view_tasks_carry_provenance_parents)]

end SwarmLean.Tests.Cli.SubIssues

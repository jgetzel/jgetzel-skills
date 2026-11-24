import SwarmLean.Db.Spawn

/-! tasks_spec.lua's asserts: reserve claims for a new agent, a lost race is `lost`, unreserve reopens; event_task parses
ids; claim's dependency check holds in its write. -/

namespace SwarmLean.Tests.Tasks
open SwarmLean SwarmLean.Tasks SwarmLean.Spawn

#guard eventTask { id := 1, data := some "#12 title" } == some 12 && eventTask { id := 1, data := some "auto #3" } == some 3
#guard eventTask { id := 1, data := some "#12x" } == none && eventTask { id := 1, data := some "t-3" } == none

/-- #1 one, #2 two after #1. -/
def db0 : Db := { tasks := [{ id := 1, title := some "one" }, { id := 2, title := some "two", deps := some "1" }],
                  taskNext := 3 }

/-- Was it a die (not a lost race)? -/
def isDie : Except Refusal Task → Bool
  | .error (.die _) => true
  | _ => false

/-- The lost race's text. -/
def lostOf : Except Refusal Task → Option String
  | .error (.lost m) => some m
  | _ => none

-- #2 waits on #1
#guard isDie (reserveTask db0 none "n1" "/r" 2 (some "sonnet") 100).2

/-- n1 reserves #1. -/
def r1 := reserveTask db0 none "n1" "/r" 1 (some "sonnet") 100

#guard (match r1.2 with | .ok r => r.title == some "one" | _ => false)
#guard (r1.1.find 1).map (fun t => (t.status, t.owner, t.first_claimed_at.isSome)) == some (.inProgress, some "n1", true)
#guard (r1.1.agents.find? (·.name == "n1")).bind (·.model) == some "sonnet"

-- a peer got it first
#guard lostOf (reserveTask r1.1 none "n2" "/r" 1 none 100).2 == some "task #1 is In Progress, owned by n1"

/-- The launch failed: n1 unreserves. -/
def u := unreserve r1.1 "n1" (match r1.2 with | .ok r => some r | _ => none) 101

#guard (u.find 1).map (fun t => (t.status, t.owner, t.first_claimed_at)) == some (.ready, none, none)
#guard ((u.agents.find? (·.name == "n1")).bind (·.ended)).isSome
-- it ends as every end does (`endRow`): status ended, its stay cleared
#guard ((u.agents.find? (·.name == "n1")).bind (·.status)) == some .ended
#guard ((unreserve (r1.1.setAgent "n1" ({ · with stay := some "x" })) "n1" none 101).agent "n1").bind (·.stay) == none

/-- #3, Ready, which a `task after` made wait on #1 (Ready again). The Lua raced it between claim's read of the deps and
its update; here claim is one step, so the step runs on the db the race left. -/
def raced : Db := { u with tasks := u.tasks ++ [{ id := 3, title := some "three", deps := some "1" }], taskNext := 4 }

#guard (match (claim { me := "n3", now := 200 } 3 "2h" raced).2 with | .error _ => true | .ok _ => false)
#guard ((claim { me := "n3", now := 200 } 3 "2h" raced).1.find 3).map (·.status) == some .ready

-- board #1810: a row's state and columns decode to a TaskState, or are refused naming what fits no state
def misfitOf (r : Except String TaskState) : Option String := match r with | .error e => some e | .ok _ => none
#guard misfitOf (TaskState.ofCols .inProgress none (some 1) none none none none none) == some "in_progress with no owner"
#guard misfitOf (TaskState.ofCols .ready none (some 1) none none none none none) == some "ready with lease_until set"
#guard misfitOf (TaskState.ofCols .completed (some "a") none none none (some "l") none none) ==
  some "completed with no land_sha, landing_at"
#guard misfitOf (TaskState.ofCols .inReview (some "a") (some 5) none none none none none) ==
  some "in_review with no land_sha, landing_at and lease_until set"
#guard misfitOf (TaskState.ofCols .duplicate none none none none none none none) == some "duplicate with no dup_of"
#guard misfitOf (TaskState.ofCols .cancelled none none none none none none (some 3)) == some "cancelled with dup_of set"
#guard (TaskState.ofCols .needsInput (some "a") (some 5) (some "q?") none none none none).toOption ==
  some (.needsInput "a" 5 "q?")
#guard (TaskState.ofCols .cancelled none none (some "q?") (some "abc") none (some 7) none).toOption ==
  some (.cancelled (some "q?") (some ⟨"abc", none, 7⟩))
-- a Ready or Backlog task may have an assignee (reserved), a Duplicate names its original
#guard (TaskState.ofCols .ready (some "human") none none none none none none).toOption == some (.ready (some "human"))
#guard (TaskState.ofCols .backlog (some "a1") none none none none none none).toOption == some (.backlog (some "a1"))
#guard (TaskState.ofCols .duplicate none none none none none none (some 4)).toOption == some (.duplicate 4 none none)
-- priorities are names; numbers are refused with the mapping
#guard (Priority.ofText "urgent", Priority.ofText "none", Priority.ofText "2") == (some .urgent, some .none, none)
#guard (Priority.ofNum (some 1), Priority.ofNum none).1.toOption == some .urgent

end SwarmLean.Tests.Tasks

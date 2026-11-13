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
#guard (r1.1.find 1).map (fun t => (t.state, t.owner, t.first_claimed_at.isSome)) == some (.claimed, some "n1", true)
#guard (r1.1.agents.find? (·.name == "n1")).bind (·.model) == some "sonnet"

-- a peer got it first
#guard lostOf (reserveTask r1.1 none "n2" "/r" 1 none 100).2 == some "task #1 is claimed, owned by n1"

/-- The launch failed: n1 unreserves. -/
def u := unreserve r1.1 "n1" (match r1.2 with | .ok r => some r | _ => none) 101

#guard (u.find 1).map (fun t => (t.state, t.owner, t.first_claimed_at)) == some (.open, none, none)
#guard ((u.agents.find? (·.name == "n1")).bind (·.ended)).isSome

/-- #3, open, which a `task after` made wait on #1 (open again). The Lua raced it between claim's read of the deps and
its update; here claim is one step, so the step runs on the db the race left. -/
def raced : Db := { u with tasks := u.tasks ++ [{ id := 3, title := some "three", deps := some "1" }], taskNext := 4 }

#guard (match (claim { me := "n3", now := 200 } 3 "2h" raced).2 with | .error _ => true | .ok _ => false)
#guard ((claim { me := "n3", now := 200 } 3 "2h" raced).1.find 3).map (·.state) == some .open

end SwarmLean.Tests.Tasks

import Tests.Cli.Fixture
import SwarmLean.Lib.Cost

/-! cost_spec.lua's asserts that need the world (its pure ones are Tests/Cost.lean's and Tests/CostTick.lean's): the
history's pruning, machine.cgroup's read of a faked /proc and cgroup tree, `cost --top`, and cost only measuring. -/

namespace SwarmLean.Tests.Spec.Cost
open SwarmLean SwarmLean.Tests.Cli
open Lean (Json toJson)

/-- Runs an App action. -/
def app (act : App α) : IO α := do
  match ← (act.run.run { conn := ← IO.mkRef none }) with
  | .ok a => pure a
  | .error e => fail s!"exit {e.code}"

-- pruning keeps 20 per (machine, repo, key)
def test_pruning_keeps_20 (_ : T) : IO Unit := do
  for i in [1:26] do
    discard <| app (Cost.record { ts := 0, machine := "h", repo := "repo", agent := "a", cmd := "make test",
                                  wall_s := 61 + i, peak_kb := 1 })
  let h ← Sqlite.Conn.open (← app Cost.path) true
  eq ((← h.query "select count(*) n from cmd where key='make test'")[0]![0]! == .int 20) true
  eq ((← h.query "select min(wall_s) m from cmd where key='make test'")[0]![0]! == .int 67) true

-- a cgroup per agent: machine.cgroup reads the agent's scope from /proc/<pid>/cgroup, its memory.peak and cpu.stat
def test_cgroup_read (t : T) : IO Unit := do
  Shim.setenv "SWARM_PROC" (t.d ++ "/proc"); Shim.setenv "SWARM_CGROUP" (t.d ++ "/cg")
  let scope := "/user.slice/swarm-agent-sr-1-7.scope"
  IO.FS.createDirAll (t.d ++ "/proc/100"); IO.FS.createDirAll (t.d ++ "/cg" ++ scope)
  eq ((← app (Machine.cgroup 100)).isNone) true
  put (t.d ++ "/proc/100/cgroup") s!"0::{scope}\n"
  put (t.d ++ "/cg" ++ scope ++ "/memory.peak") (toString (1000 * 1024))
  put (t.d ++ "/cg" ++ scope ++ "/cpu.stat") "usage_usec 5000000\n"
  eq ((← app (Machine.cgroup 100)).map fun c => (c.peak_kb, c.cpu_s)) (some (1000, 5))

-- cost --top runs
def test_cost_top (t : T) : IO Unit := t.sw_ "a" ["cost", "--top"]

-- nothing here signals a process or writes oom_score_adj outside an agent's tree (the tick only reads)
def test_cost_only_measures (_ : T) : IO Unit := do
  let src ← IO.FS.readFile s!"{← swarmDir}/lean/SwarmLean/Lib/Cost.lean"
  hasnt src "oom_score_adj"; hasnt src "SIGTERM"; hasnt src "signal"

def tests : List Case := [
  ("test_pruning_keeps_20", test_pruning_keeps_20),
  ("test_cgroup_read", test_cgroup_read),
  ("test_cost_top", test_cost_top),
  ("test_cost_only_measures", test_cost_only_measures)]

end SwarmLean.Tests.Spec.Cost

import SwarmLean.Lib.Compute

/-! sw-compute.md §5: sizing from the history, as a pure function (the script's answers and the `ls` rendering are claim/Tests/Ledger.lean's). -/

open SwarmLean Compute

#guard size [] == none
#guard size [(0, 5, 5, "swarm")] == none
-- cores: the default, raised by the largest cpu_s/wall_s of a row with cpu_s > 0 that is not source run; peak × 1.25 from every row
#guard size [(100, 400, 1000000, "swarm"), (60, 61, 2000000, "swarm")] == some (4, 2500000)
#guard size [(100, 0, 0, "swarm")] == some (2, DEFAULT_MEM_KB)
#guard size [(100, 101, 1000, "swarm")] == some (2, 1250)
#guard size [(100, 900, 1000, "run")] == some (9, 1250)
#guard size [(100, 0, 1000, "run")] == some (2, 1250)
#guard size [(100, 900, 4000, "run"), (100, 0, 100, "swarm")] == some (9, 5000)

/-- `run` rows of these walls. -/
def runs (ws : List Nat) : List (Int × Int × Int × String) := ws.map (fun (w : Nat) => ((w : Int), (0 : Int), (0 : Int), "run"))
-- the estimate: the nearest-rank 90th percentile of the `run` rows with a wall time; none without one
#guard estimate [] == none
#guard estimate [(0, 0, 0, "run")] == none
#guard estimate [(100, 5, 5, "swarm"), (900, 0, 0, "repo")] == none
#guard estimate (runs (List.range' 1 10)) == some 9
#guard estimate (runs (List.range' 1 4)) == some 4
#guard estimate (runs (List.range' 1 50)) == some 45
#guard estimate (runs [7]) == some 7
#guard estimate (runs [3, 1000, 2]) == some 1000
-- unsorted, with a zero wall and a `swarm` row of 1000 s that do not count
#guard estimate (runs (List.range' 1 12).reverse ++ [(1000, 0, 0, "swarm"), (0, 0, 0, "run")]) == some 11

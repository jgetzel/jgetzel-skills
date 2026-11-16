import SwarmLean.Lib.Compute

/-! sw-compute.md §5: sizing from the history, as a pure function (the script's answers and the `ls` rendering are claim/Tests/Ledger.lean's). -/

open SwarmLean Compute

#guard size [] == none
#guard size [(0, 5, 5, "swarm")] == none
-- cores: the default, raised by the largest cpu_s/wall_s of a row with cpu_s > 0 that is not source run; peak × 1.25 from every row
#guard size [(100, 400, 1000000, "swarm"), (60, 61, 2000000, "swarm")] == some (4, 2500000)
#guard size [(100, 0, 0, "swarm")] == some (2, DEFAULT_MEM_KB)
#guard size [(100, 101, 1000, "swarm")] == some (2, 1250)
#guard size [(100, 900, 1000, "run")] == some (2, 1250)
#guard size [(100, 900, 4000, "run"), (100, 0, 100, "swarm")] == some (2, 5000)

import SwarmLean.Lib.Compute

/-! sw-compute.md §5: sizing from the history, the script's answers and the `ls` rendering, as pure functions. -/

open SwarmLean Compute

#guard size [] == none
#guard size [(0, 5, 5, "swarm")] == none
-- cores: the default, raised by the largest cpu_s/wall_s of a row with cpu_s > 0 that is not source run; peak × 1.25 from every row
#guard size [(100, 400, 1000000, "swarm"), (60, 61, 2000000, "swarm")] == some (4, 2500000)
#guard size [(100, 0, 0, "swarm")] == some (2, DEFAULT_MEM_KB)
#guard size [(100, 101, 1000, "swarm")] == some (2, 1250)
#guard size [(100, 900, 1000, "run")] == some (2, 1250)
#guard size [(100, 900, 4000, "run"), (100, 0, 100, "swarm")] == some (2, 5000)

#guard parseTry "ok 4" == .ok 4
#guard parseTry "wait 2 1024 3" == .wait 2 1024 3
#guard parseTry "never 8 16" == .never 8 16
#guard parseTry "off" == .off
#guard parseTry "" == .gone
#guard parseTry "wait 2" == .gone

def lsSample : String := "20 9.30 25165824 64161000 20 83886080 0
c 6 8388608 p31 700 sr-3 nix build .#x
c 2 2097152 t999 800 sr-5 cargo test
q 880 12 2097152 sr-7
"

#guard (parseLs lsSample).map (fun l => (l.ncpu, l.cap_mem_kb, l.off, l.claims.length, l.queue.length)) == some (20, 83886080, false, 2, 1)
#guard (parseLs lsSample).bind (·.claims.head?) == some { cores := 6, mem_kb := 8388608, holder := "p31", start := 700, who := "sr-3", cmd := "nix build .#x" }
#guard (parseLs "1 2").isNone
#guard ((parseLs lsSample).map (render "here" · 1000)) == some [
  "here: 8 of 20 cores claimed (cap 20 of 20, 9.3 busy), 10.0 of 80.0G claimed (61.2G available)",
  "  sr-3   6 cores  8.0G  5m  nix build .#x",
  "  sr-5   2 cores  2.0G  3m  cargo test",
  "  waiting: sr-7 12 cores 2.0G 2m"]
#guard ((parseLs "8 0.00 100 100 8 100 1\n").map (render "desktop" · 0)) == some ["desktop: off"]

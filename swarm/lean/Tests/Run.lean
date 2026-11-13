import SwarmLean.Lib.Run
import SwarmLean.Cmd.Run

/-! machine_spec.lua's asserts on run.lua's probe reader, and main.lua's split of `swarm run`'s command. -/

open SwarmLean Run

/-- machine_spec's vm_stat. -/
def vmRun : String := "Mach Virtual Memory Statistics: (page size of 16384 bytes)
Pages free:                               12345.
Pages active:                            200000.
Pages inactive:                          100000.
Pages speculative:                         5000.
Pages throttled:                              0.
Pages wired down:                         80000.
Pages purgeable:                           2655.
"

#guard parseProbe ("@darwin\n10\n34359738368\n1\n{ 3.21 2.00 1.00 }\n" ++ vmRun) ==
  some { cores := 10, load := 3.21, avail_kb := 120000 * 16, total_kb := 32 * 2 ^ 20, level := some "normal" }
#guard parseProbe "24\n3.50 2.0 1.0 1/900 77\nMemTotal: 1000 kB\nMemAvailable: 400 kB\nsome avg10=2.50 avg60=0\n" ==
  some { cores := 24, load := 3.5, avail_kb := 400, total_kb := 1000, psi := some 2.5 }
#guard parseProbe "@darwin\n\n\n\n\n" == none
#guard Cmd.Run.split ["--on", "laptop", "--env", "K=1", "--", "make", "--on"] == (["--on", "laptop", "--env", "K=1"], ["make", "--on"])
#guard Cmd.Run.split ["echo hi; exit 2"] == ([], ["echo hi; exit 2"])

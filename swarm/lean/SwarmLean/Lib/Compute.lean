import Claims.Ledger
import SwarmLean.Sys
import SwarmLean.Lib.Json
import SwarmLean.Lib.Cost

/-! sw-compute.md: sized claims on a machine's cores and memory. The ledger, its script and the claim loop are the `claim` tool
(../../claim, `Claims`); this file sizes a job from the cmd-cost history and gives the tool swarm's `Proc`/`Sys`/`Clock`/`Env`. -/

namespace SwarmLean.Compute
open Lean (Json)

/-- With no history, what a job claims. -/
def DEFAULT_CORES : Int := 2
/-- ... and its memory (KiB): 2 GiB. -/
def DEFAULT_MEM_KB : Int := 2097152

/-- The tool's world, from swarm's classes: argv runs as `Proc.output` runs it. -/
def host {m : Type → Type} [Monad m] [Proc m] [Sys m] [Clock m] [Env m] : Claims.Host m where
  run argv := return (← Proc.output argv none []).map fun r => (Int.ofNat r.code.toNat, r.stdout)
  sleep ms := Sys.sleep ms
  err s := Env.err s
  out s := Env.out s
  now := Clock.now

/-- What a job claims, from its history rows (wall_s, cpu_s, peak_kb, source) on any machine: cores are the default or the
largest `cpu_s / wall_s` rounded up over rows with a CPU reading that `swarm run` did not itself record (`source` run holds
a %CPU sample), whichever is more, so history only raises it; memory is the largest peak × 1.25 over every row; none
without a row that has a wall time. -/
def size (rows : List (Int × Int × Int × String)) : Option (Int × Int) :=
  let rs := rows.filter (·.1 > 0)
  if rs.isEmpty then none else
  let cores := rs.foldl (fun a r => if r.2.1 > 0 && r.2.2.2 != "run" then max a ((r.2.1 + r.1 - 1) / r.1) else a) DEFAULT_CORES
  let peak := rs.foldl (fun a r => max a r.2.2.1) 0
  some (cores, if peak ≤ 0 then DEFAULT_MEM_KB else (peak * 5 + 3) / 4)

/-- The cmd-cost rows (wall_s, cpu_s, peak_kb) of this repo's command `line`, from any machine. -/
def history {m : Type → Type} [Monad m] [Env m] [Sys m] [Git m] (line : String) : m (List (Int × Int × Int × String)) := do
  if !(← Cost.exists?) then return []
  let some repo ← Cost.repoName | return []
  let rows := ((← Sys.sqlAt (← Cost.path) Cost.SCHEMA [("select wall_s,cpu_s,peak_kb,source from cmd where repo=? and key=?",
    [.text repo, .text (Cost.key line)])]).headD #[]).toList
  return rows.map fun r => (Cost.vi (r.getD 0 .null), Cost.vi (r.getD 1 .null), Cost.vi (r.getD 2 .null), Cost.vs (r.getD 3 .null))

end SwarmLean.Compute

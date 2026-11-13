import SwarmLean.World
import SwarmLean.Lib.Json

/-! ci.lua: the flows of `.claude/swarm.json`, GitHub's time stamps and a PR's check verdict. -/

namespace SwarmLean.Ci
open Lean (Json)

variable {m : Type → Type} [Monad m]

/-- "2026-11-08T10:00:00Z" as epoch seconds (UTC), as Python's fromisoformat(...).timestamp() (ci.ts). -/
def ts (s : String) : Int :=
  let num (i n : Nat) : Int := ((s.drop i |>.take n).toString.toNat?.getD 0 : Nat)
  let (y, mo, dd) := (num 0 4, num 5 2, num 8 2)
  let y := if mo ≤ 2 then y - 1 else y
  let era := Int.fdiv y 400
  let mp := Int.emod (mo + 9) 12
  let yoe := y - era * 400
  let doe := yoe * 365 + Int.fdiv yoe 4 - Int.fdiv yoe 100 + Int.fdiv (153 * mp + 2) 5 + dd - 1
  (era * 146097 + doe - 719468) * 86400 + num 11 2 * 3600 + num 14 2 * 60 + num 17 2

/-- `.claude/swarm.json`'s `ci` object at the repo's top, or {} (ci_cfg). -/
def ciCfg [Git m] [Fs m] (repo : Option String) : m Json := do
  let top := (← Git.git ["rev-parse", "--show-toplevel"] repo).map strip
  let txt ← match top with
    | some t => pure ((← Fs.read s!"{t}/.claude/swarm.json").getD "")
    | none => pure ""
  match (Json.decode txt).bind (Json.field · "ci") with
  | some c@(.obj _) => return c
  | _ => return Json.mkObj []

/-- The flows `ci.flow` may name (ci.FLOWS). -/
def FLOWS : List String := ["none", "post-merge", "pr-gated", "promoted"]

/-- The spawn message's CI line for each flow (ci.FLOW_LINE). -/
def FLOW_LINE : String → Option String
  | "none" => some "CI here (`ci.flow` none): there is no CI; land on green local checks."
  | "post-merge" => some ("CI here (`ci.flow` post-merge, or unset): land on green local checks and don't wait for CI; a red run " ++
      "on the base becomes one `main red: …` task, done by watchd on the next green run.")
  | "pr-gated" => some ("CI here (`ci.flow` pr-gated): the PR's checks gate the merge. `swarm stay \"CI on PR #N, then merge\"` and " ++
      "stop; watchd wakes you when they finish: merge on green, fix and push on red.")
  | "promoted" => some ("CI here (`ci.flow` promoted): land on the dev base your task names, as post-merge: green local checks, " ++
      "don't wait for CI.")
  | _ => none

/-- The repo's CI flow, none when unset or not one of FLOWS (ci.flow). -/
def flow [Git m] [Fs m] (repo : Option String) : m (Option String) := do
  return (Json.fstr (← ciCfg repo) "flow").filter FLOWS.contains

/-- A PR's checks from gh's statusCheckRollup: green, red or pending (ci.verdict). -/
def verdict (rollup : Option Json) : String := Id.run do
  let some (.arr xs) := rollup | return "pending"
  if xs.isEmpty then return "pending"
  let mut red := false
  for x in xs do
    let st := if Json.fstr x "__typename" == some "StatusContext" then Json.fstr x "state"
      else if Json.fstr x "status" == some "COMPLETED" then Json.fstr x "conclusion" else none
    match st with
    | none | some "" | some "PENDING" | some "EXPECTED" => return "pending"
    | some s => if s != "SUCCESS" && s != "NEUTRAL" && s != "SKIPPED" then red := true
  return if red then "red" else "green"

/-- The poll's decision on a claimed task's PR (ci.pr_act): done once merged; wake once its checks finished in a
pr-gated repo and the owner was not told. -/
def prAct (state verdict : String) (gated told : Bool) : Option String :=
  if state == "MERGED" then some "done"
  else if gated && state == "OPEN" && verdict != "pending" && !told then some "wake" else none

end SwarmLean.Ci

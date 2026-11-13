import SwarmLean.Cmd
import SwarmLean.Cmd.OpsHelp
import SwarmLean.Lib.Cost

/-! `swarm cost` (cost.cmd_cost): what a command took here before, or the most intensive ones. -/

namespace SwarmLean.Cmd.Cost
open Args _root_.SwarmLean.Cost

/-- The `cost` parser. -/
def spec : Spec :=
  .mk "cost" helpCost [{ name := "words", minArgs := 0, maxArgs := 1000000 }]
    [flag "--top", opt "--repo", flag "--all-repos"] [] [] none

variable {m : Type → Type} [Monad m] [MonadExceptOf Exit m] [Env m] [Sys m] [Git m]

/-- `swarm cost …`. -/
def cost (a : Parsed) : m UInt32 := do
  let out := Env.out (m := m)
  if !(← exists?) then
    out "no history yet (watchd records commands that run a minute or take 1G)"
    return 0
  let repo ← match a.str "repo" with
    | some r => pure (some r)
    | none => repoName
  let host ← Sys.hostname
  let p ← path
  if a.flag "top" then
    let all := a.flag "all_repos"
    let (whr, args) := if all then ("where machine=?", [Sqlite.Val.text host])
      else ("where machine=? and repo=?", [.text host, match repo with | some r => .text r | none => .null])
    for (col, name) in [("peak_kb", "peak"), ("cpu_s", "cpu")] do
      out s!"by {name}:"
      let rows := ((← Sys.sqlAt p SCHEMA [(s!"select repo,key,count(*) n,max(peak_kb) peak,max(cpu_s) cpu,max(wall_s) wall from cmd {whr} group by repo,key order by max({col}) desc limit 5", args)]).headD #[])
      for r in rows do
        let n := vi (r.getD 2 .null)
        out s!"  {if all then vs (r.getD 0 .null) ++ " " else ""}{vs (r.getD 1 .null)}: {n} run{if n == 1 then "" else "s"}, peak {gib (vi (r.getD 3 .null))}, {mins (vi (r.getD 5 .null))}, {cpuMin (vi (r.getD 4 .null))} CPU-min"
    return 0
  let ws := a.strs "words"
  if ws.isEmpty then die "swarm cost \"<command>\" or swarm cost --top"
  let k := key (" ".intercalate ws)
  let rows := ((← Sys.sqlAt p SCHEMA [("select wall_s,cpu_s,peak_kb from cmd where machine=? and repo=? and key=?",
    [.text host, match repo with | some r => .text r | none => .null, .text k])]).headD #[]).toList
  out ((summaryOf k (rows.map fun r => (vi (r.getD 0 .null), vi (r.getD 1 .null), vi (r.getD 2 .null)))).getD
    s!"no history for `{k}` here")
  return 0

/-- The group: cost. -/
def group : Group m where
  specs := [("cost", spec)]
  run := cost

end SwarmLean.Cmd.Cost

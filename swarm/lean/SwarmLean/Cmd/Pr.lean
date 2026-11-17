import SwarmLean.Cmd
import SwarmLean.Cmd.OpsHelp
import SwarmLean.Lib.Merge
import SwarmLean.Sys

/-! `swarm pr merge-when-green <pr>...` (orchestrate/merge-retry.sh): squash-merges each PR once its head's checks are green. -/

namespace SwarmLean.Cmd.Pr
open Args Merge

/-- The `pr` parser and its subcommand. -/
def spec : Spec :=
  .mk "pr" helpPr [] [] [] (cmdTarget := some "act") (cmds := [
    .mk "merge-when-green" helpPrMergeWhenGreen [{ name := "prs", maxArgs := 1000000 }]
      [opt "--every" (some "180") (some int), opt "--polls" (some "40") (some int)] [] [] none])

variable {m : Type → Type} [Monad m] [MonadExceptOf Exit m] [Clock m] [Env m] [Proc m] [Sys m]

/-- `gh pr view` of PR `n`: what it printed, none when it failed. -/
def ghView (n : Nat) : m (Option String) := do
  match ← Proc.output ["gh", "pr", "view", toString n, "--json", VIEW_FIELDS] none [] with
  | some o => return if o.code == 0 then some o.stdout else none
  | none => return none

/-- Squash-merges a green head, matching its sha. -/
def merge (g : GreenHead) : m Unit := discard <| Proc.output g.mergeArgv none []

/-- One look at PR `n`: true once it is merged, else what it waits with. -/
def step (n : Nat) : m Bool := do
  let stamp ← do pure s!"{← Clock.hhmm (← Clock.now)} #{n}"
  let resp ← ghView n
  if resp.bind stateOf == some "MERGED" then Env.out s!"{stamp} merged"; return true
  if let some g := resp.bind (GreenHead.parse n) then
    merge g
    if (← ghView n).bind stateOf == some "MERGED" then Env.out s!"{stamp} merged @{g.sha.take 7}"; return true
  Env.out s!"{stamp} waiting: {match resp with | some r => waiting r | none => "api-error"}"
  return false

/-- `swarm pr merge-when-green …`: every `--every` seconds, `--polls` times, each PR left whose head is green. Exit 0
when all are merged, else 1. -/
def mergeWhenGreen (a : Parsed) : m UInt32 := do
  let mut left := []
  for s in a.strs "prs" do
    match s.toNat? with
    | some n => left := left ++ [n]
    | none => die s!"not a PR number: '{s}'"
  let every := ((a.int "every").getD 180).toNat
  let polls := ((a.int "polls").getD 40).toNat
  for i in [0:polls] do
    let mut next := []
    for n in left do
      unless ← step n do next := next ++ [n]
    left := next
    if left.isEmpty then Env.out "ALL MERGED"; return 0
    if i + 1 < polls then Sys.sleep (every * 1000)
  Env.out s!"gave up after 2h: {" ".intercalate (left.map toString)}"
  return 1

/-- The group: pr. -/
def group : Group m where
  specs := [("pr", spec)]
  run a := match a.act with
    | "merge-when-green" => mergeWhenGreen a
    | _ => return 2

end SwarmLean.Cmd.Pr

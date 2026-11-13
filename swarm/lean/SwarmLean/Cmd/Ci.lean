import SwarmLean.Cmd
import SwarmLean.Cmd.OpsHelp
import SwarmLean.Lib.Ci
import SwarmLean.Sys

/-! `swarm ci [sha]` (ci.cmd_ci): main's CI for a commit, from what watchd polled; never asks GitHub. -/

namespace SwarmLean.Cmd.Ci
open Args _root_.SwarmLean.Ci

/-- Lua's `tonumber` for an option: a decimal number, kept as its text. -/
def num : Conv := fun s =>
  let t := strip s
  let t' := if t.startsWith "-" || t.startsWith "+" then (t.drop 1).toString else t
  if (parseFloat t').isSome then .ok (.s t) else .error none

/-- A `num` option's value as a float. -/
def numVal (s : Option String) (dflt : Float) : Float :=
  match s with
  | some t =>
    let t := strip t
    if t.startsWith "-" then -((parseFloat (t.drop 1).toString).getD 0)
    else (parseFloat ((if t.startsWith "+" then (t.drop 1).toString else t))).getD dflt
  | none => dflt

/-- The `ci` parser. -/
def spec : Spec :=
  .mk "ci" helpCi [{ name := "sha", minArgs := 0, default := some "HEAD" }]
    [flag "--wait", opt "--timeout" (some "3600") (some int), opt "--poll" (some "10") (some num)] [] [] none

variable {m : Type → Type} [Monad m] [MonadExceptOf Exit m] [Store m] [Clock m] [Env m] [Proc m] [Git m] [Sys m]

/-- `swarm ci …`. Exit 0 green, 1 red, 2 pending, 124 timed out waiting. -/
def ci (a : Parsed) : m UInt32 := do
  let cwd ← Env.cwd
  let arg := (a.str "sha").getD "HEAD"
  let sha := ((← Git.git ["rev-parse", arg] (some cwd)).map strip).getD arg
  let timeout := (a.int "timeout").getD 3600
  let poll := numVal (a.str "poll") 10
  let deadline := (← Clock.now) + timeout
  let mut fetched : Int := 0
  let mut warned := false
  let mut res : String × Option _root_.SwarmLean.Ci := ("pending", none)
  repeat
    let db ← Store.txn [.ci, .«meta»] fun db => (db, db)
    let now ← Clock.now
    let polled := (db.getMeta "ci_polled").map fun r => (r.v.bind parseInt).getD 0
    if (polled.all (now - · > 300)) && !warned then
      warned := true
      Env.err "swarm ci: nobody is polling CI (the communicator runs `swarm watchd --ci`); tell it."
    res ← ciFor db.cis sha (some cwd)
    if res.1 != "pending" || !a.flag "wait" then break
    if (← Clock.now) ≥ deadline then
      Env.err s!"{short sha}: still pending after {d timeout}s"
      return 124
    if (← Clock.now) - fetched ≥ 60 then
      discard <| Proc.output ["git", "fetch", "-q", "origin"] (some cwd) []
      fetched ← Clock.now
    Sys.sleep (poll * 1000).toUInt64.toNat
  let (state, r) := res
  match r with
  | none => Env.out s!"{short sha}: no main CI run includes it yet"
  | some r =>
    let failed := match r.failed with | some f => if f != "" then "; failed: " ++ f else "" | none => ""
    let wf := match r.workflow with | some w => if w != "" then w ++ " " else "" | none => ""
    Env.out s!"{short sha}: {state} ({wf}run {d r.id} at {short r.sha} {r.url.getD ""}{failed})"
  return if state == "success" then 0 else if state == "failure" then 1 else 2

/-- The group: ci. -/
def group : Group m where
  specs := [("ci", spec)]
  run := ci

end SwarmLean.Cmd.Ci

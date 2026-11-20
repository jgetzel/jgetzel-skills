import SwarmLean.Cmd
import SwarmLean.Cmd.OpsHelp
import SwarmLean.Lib.Compute
import Claims.Cli

/-! `swarm compute` (sw-compute.md §4): the claims on this machine and every hc machine; the caps and the off switch. It is
`claim` (../../claim) with swarm's world. -/

namespace SwarmLean.Cmd.Compute
open Args _root_.SwarmLean.Compute

/-- The `compute` parser. -/
def spec : Spec :=
  .mk "compute" helpCompute [{ name := "words", minArgs := 0, maxArgs := 4 }]
    [flag "--json", opt "--cores", opt "--mem", opt "--id", opt "--who", opt "--est", opt "--ttl", opt "--pid", opt "--owner"] [] [] none

variable {m : Type → Type} [Monad m] [MonadExceptOf Exit m] [Clock m] [Env m] [Proc m] [Sys m]

/-- `swarm compute …`. -/
def compute (a : Parsed) : m UInt32 := do
  match ← Claims.compute host "swarm compute" (a.strs "words") (a.flag "json") (a.str "cores") (a.str "mem")
      { id := a.str "id", who := a.str "who", est := a.str "est", ttl := a.str "ttl", pid := a.str "pid", owner := a.str "owner" }
      (a.strs "argv") with
  | .ok () => return 0
  | .error e => die e

/-- The group: compute. -/
def group : Group m where
  specs := [("compute", spec)]
  run := compute

end SwarmLean.Cmd.Compute

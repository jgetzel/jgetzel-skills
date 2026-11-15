import SwarmLean.Cmd
import SwarmLean.Cmd.OpsHelp
import SwarmLean.Lib.Compute
import SwarmLean.Lib.Run

/-! `swarm compute` (sw-compute.md §4): the claims on this machine and every hc machine; the caps and the off switch. -/

namespace SwarmLean.Cmd.Compute
open Args _root_.SwarmLean.Compute _root_.SwarmLean.Run
open Lean (Json)

/-- The `compute` parser. -/
def spec : Spec :=
  .mk "compute" helpCompute [{ name := "words", minArgs := 0, maxArgs := 3 }] [flag "--json", opt "--cores", opt "--mem"] [] [] none

variable {m : Type → Type} [Monad m] [MonadExceptOf Exit m] [Clock m] [Env m] [Proc m] [Sys m]

/-- `swarm compute …`. -/
def compute (a : Parsed) : m UInt32 := do
  let ms ← hcMachines
  let target (n : String) : m (Option String) := do
    if n == "here" then return none
    if (ms.lookup n).isNone then die s!"no machine {n} in `hc machine ls`"
    return some n
  match a.strs "words" with
  | [] =>
    let now ← Clock.now
    let all : List (String × Option String) := ("here", none) :: ms.map fun (n, _) => (n, some n)
    let mut out := []
    let mut js := []
    for (n, c) in all do
      let st := match c with | none => "connected" | some _ => ((ms.lookup n).bind (Json.fstr · "state")).getD "?"
      let l ← if st == "connected" then pure ((← sh c ["ls"]).bind parseLs) else pure none
      match l with
      | some l => out := out ++ render n l now; js := js ++ [(n, l.json)]
      | none =>
        let s := if st == "connected" then "unreachable" else st
        out := out ++ [s!"{n}: {s}"]; js := js ++ [(n, Json.mkObj [("state", .str s)])]
    if a.flag "json" then Env.out (Json.mkObj js).compress else for l in out do Env.out l
  | ["cap", n] =>
    let c ← target n
    let cores ← match a.str "cores" with
      | none => pure "="
      | some "all" => pure "-"
      | some x => if (parseInt x).any (· ≥ 1) then pure x else die s!"--cores: not a count: {x}"
    let mem ← match a.str "mem" with
      | none => pure "="
      | some "all" => pure "-"
      | some x => match parseFloat x with
        | some g => pure (d (Int.ofNat (g * 1048576).floor.toUInt64.toNat))
        | none => die s!"--mem: not a size in G: {x}"
    if (← sh c ["cap", cores, mem]).isNone then die s!"{n}: no answer"
  | [w, n] =>
    if w != "off" && w != "on" then die "swarm compute [--json] | cap <machine|here> [--cores N|all] [--mem G|all] | off|on <machine|here>"
    if (← sh (← target n) [w]).isNone then die s!"{n}: no answer"
  | _ => die "swarm compute [--json] | cap <machine|here> [--cores N|all] [--mem G|all] | off|on <machine|here>"
  return 0

/-- The group: compute. -/
def group : Group m where
  specs := [("compute", spec)]
  run := compute

end SwarmLean.Cmd.Compute

import Lean
import SwarmModel

/-! check.sh's gate (board #34): every theorem of SwarmModel rests on Lean's three axioms (propext, Classical.choice,
Quot.sound) and the named, documented environment assumptions of SwarmModel/Env.lean, and nothing else (no sorryAx, no
Lean.ofReduceBool from native_decide). Prints each theorem that uses an environment assumption, with them. -/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let modOf (n : Name) : Name := match env.getModuleIdxFor? n with
    | some i => env.header.moduleNames[i.toNat]!
    | none => `SwarmModel  -- this file
  let core : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let envAx := env.constants.fold (init := #[]) fun acc n ci =>
    if ci matches .axiomInfo _ && modOf n == `SwarmModel.Env then acc.push n else acc
  for a in envAx do
    if (← findDocString? env a).isNone then throwError "{a}: an environment assumption without a docstring"
  let thms := env.constants.fold (init := #[]) fun acc n ci =>
    if ci matches .thmInfo _ && (`SwarmModel).isPrefixOf (modOf n) && !n.isInternal then acc.push n else acc
  let mut plain := 0
  let mut bad := #[]
  let mut lines := #[]
  for n in thms do
    let axs ← collectAxioms n
    let extra := axs.filter (!core.contains ·)
    if extra.isEmpty then plain := plain + 1
    else
      let wrong := extra.filter (!envAx.contains ·)
      if !wrong.isEmpty then bad := bad.push s!"{n}: {wrong.toList}"
      lines := lines.push s!"{n}: {extra.qsort Name.lt |>.toList}"
  for l in lines.qsort (· < ·) do logInfo l
  logInfo s!"{plain} theorems rest on Lean's axioms alone; {lines.size} use more ({envAx.size} environment assumptions in Env.lean)"
  unless bad.isEmpty do throwError "axioms outside Env.lean:\n{String.intercalate "\n" bad.toList}"

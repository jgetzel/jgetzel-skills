import Lean
import SwarmModel

/-! check.sh's gate (board #34, #68): every theorem of SwarmModel rests on Lean's three axioms (propext,
Classical.choice, Quot.sound) and nothing else (no sorryAx, no Lean.ofReduceBool from native_decide, and no assumption
about the world: those are hypotheses). Each environment hypothesis (a `Tools → Prop` or `Db → Prop` of Env.lean) has a
docstring naming its test case. Prints each theorem whose statement takes environment hypotheses, with them. -/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let modOf (n : Name) : Name := match env.getModuleIdxFor? n with
    | some i => env.header.moduleNames[i.toNat]!
    | none => `SwarmModel  -- this file
  let core : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let isHyp (ci : ConstantInfo) : Bool := match ci with
    | .defnInfo d => match d.type with
      | .forallE _ (.const t _) (.sort .zero) _ => t == ``Swarm.Env.Tools || t == ``Swarm.Env.Db
      | _ => false
    | _ => false
  let hyps := env.constants.fold (init := #[]) fun acc n ci =>
    if modOf n == `SwarmModel.Env && isHyp ci then acc.push n else acc
  for h in hyps do
    let ok := match ← findDocString? env h with
      | some d => (d.splitOn "env_spec: ").length > 1 || (d.splitOn "sqlite_spec: ").length > 1
      | none => false
    unless ok do throwError "{h}: an environment hypothesis with no (env_spec: …) or (sqlite_spec: …) tag"
  let thms := env.constants.fold (init := #[]) fun acc n ci =>
    if ci matches .thmInfo _ && (`SwarmModel).isPrefixOf (modOf n) && !n.isInternal then acc.push (n, ci) else acc
  let mut plain := 0
  let mut bad : Array String := #[]
  let mut lines : Array String := #[]
  for (n, ci) in thms do
    let extra := (← collectAxioms n).filter (!core.contains ·)
    unless extra.isEmpty do bad := bad.push s!"{n}: {extra.toList}"
    let used := hyps.filter fun h => ci.type.getUsedConstants.contains h
    if used.isEmpty then plain := plain + 1
    else lines := lines.push s!"{n}: {used.qsort Name.lt |>.toList}"
  for l in lines.qsort (· < ·) do logInfo l
  logInfo s!"{plain} theorems name no environment hypothesis; {lines.size} name some, taking them or (consistent, Trust.lean) proving them of a machine ({hyps.size} hypotheses in Env.lean)"
  unless bad.isEmpty do throwError "axioms beyond Lean's three:\n{String.intercalate "\n" bad.toList}"

import Lean
import Claims

/-! check.sh's gate: every theorem of `Claims` rests on Lean's three axioms (propext, Classical.choice, Quot.sound) and
nothing else: no sorryAx, no Lean.ofReduceBool from native_decide, no axiom about the world. What a proof assumes about the
world will be a definition of Claims/Assumptions.lean that a theorem takes as a hypothesis, each tagged `(claims_spec: …)`
with a case of `claim-tests --list`; there is none yet. Prints every theorem with its axioms, then the theorem count. -/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let modOf (n : Name) : Name := match env.getModuleIdxFor? n with
    | some i => env.header.moduleNames[i.toNat]!
    | none => `Audit
  let ours (n : Name) : Bool := (`Claims).isPrefixOf (modOf n)
  -- equation lemmas Lean generates for a definition (`f.eq_1`, `f.eq_def`) are not ours to count
  let eqn (n : Name) : Bool := match n with
    | .str _ s => s.startsWith "eq_" || s == "eq_def"
    | _ => false
  let core : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let thms := (env.constants.toList.filter fun (n, ci) => ci matches .thmInfo _ && ours n && !n.isInternal && !eqn n).toArray
    |>.qsort (fun a b => Name.lt a.1 b.1)
  let mut bad : Array String := #[]
  for (n, _) in thms do
    let ax := (← liftCoreM (collectAxioms n)).qsort Name.lt
    logInfo m!"{n}: {ax.toList}"
    let extra := ax.filter (!core.contains ·)
    unless extra.isEmpty do bad := bad.push s!"{n}: {extra.toList}"
  logInfo m!"{thms.size} theorems"
  unless bad.isEmpty do throwError "axioms beyond Lean's three:\n{String.intercalate "\n" bad.toList}"

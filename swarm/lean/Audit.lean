import Lean
import SwarmLean

/-! check.sh's gate (board #109): every theorem of swarm-lean (and of the swarm/model files it builds, Glob.lean and
Decide.lean, which run in the binary) rests on Lean's three axioms (propext, Classical.choice, Quot.sound) and nothing
else: no sorryAx, no Lean.ofReduceBool from native_decide, no axiom about the world. What the proofs assume about the
world is a definition of SwarmLean/Assumptions.lean that a theorem takes as a hypothesis; each has a doc comment with an
(env_spec: …) or (sqlite_spec: …) tag naming its test. Prints every theorem with its axioms, then each assumption with
the number of theorems whose statement takes it, and those theorems. -/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let modOf (n : Name) : Name := match env.getModuleIdxFor? n with
    | some i => env.header.moduleNames[i.toNat]!
    | none => `Audit
  let ours (n : Name) : Bool := let m := modOf n; (`SwarmLean).isPrefixOf m || (`SwarmModel).isPrefixOf m
  -- equation lemmas Lean generates for a definition (`f.eq_1`, `f.eq_def`) are not ours to count
  let eqn (n : Name) : Bool := match n with
    | .str _ s => s.startsWith "eq_" || s == "eq_def"
    | _ => false
  let core : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let tagged (n : Name) : CommandElabM Bool := do
    match ← findDocString? env n with
    | some d => return (d.splitOn "(env_spec: ").length > 1 || (d.splitOn "(sqlite_spec: ").length > 1
    | none => return false
  let mut assumptions : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if modOf n == `SwarmLean.Assumptions && ci matches .defnInfo _ && !n.isInternal && (← tagged n) then
      assumptions := assumptions.push n
  assumptions := assumptions.qsort Name.lt
  let thms := (env.constants.toList.filter fun (n, ci) => ci matches .thmInfo _ && ours n && !n.isInternal && !eqn n).toArray
    |>.qsort (fun a b => Name.lt a.1 b.1)
  let mut bad : Array String := #[]
  for (n, _) in thms do
    let ax := (← liftCoreM (collectAxioms n)).qsort Name.lt
    logInfo m!"{n}: {ax.toList}"
    let extra := ax.filter (!core.contains ·)
    unless extra.isEmpty do bad := bad.push s!"{n}: {extra.toList}"
  for a in assumptions do
    let users := thms.filter fun (_, ci) => ci.type.getUsedConstants.contains a
    logInfo m!"assumption {a}: {users.size} theorems{if users.isEmpty then "" else ": " ++ ", ".intercalate (users.toList.map (toString ·.1))}"
  let plain := thms.filter fun (_, ci) => !assumptions.any (ci.type.getUsedConstants.contains ·)
  logInfo m!"{thms.size} theorems, {plain.size} of them taking no assumption; {assumptions.size} assumptions in SwarmLean/Assumptions.lean"
  unless bad.isEmpty do throwError "axioms beyond Lean's three:\n{String.intercalate "\n" bad.toList}"

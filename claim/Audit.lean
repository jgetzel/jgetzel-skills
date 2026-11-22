import Lean
import Claims

/-! check.sh's gate: every theorem of `Claims` rests on Lean's three axioms (propext, Classical.choice, Quot.sound) and
nothing else: no sorryAx, no Lean.ofReduceBool from native_decide, no axiom about the world. What a proof assumes about the
world is a definition of Claims/Assumptions.lean that a theorem takes as a hypothesis, each tagged `(claims_spec: …)`
with cases of `claim-tests --list`. Prints every theorem with its axioms, the theorem count, then per assumption the
theorems taking it and an `assumption-case claims_spec <case>` line per tagged case, which check.sh looks up in
`claim-tests --list`. Fails on an assumption with no tag or no theorem taking it. -/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let modOf (n : Name) : Name := match env.getModuleIdxFor? n with
    | some i => match env.header.moduleNames[i.toNat]? with | some m => m | none => `Audit
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
  let asms := env.constants.toList.filter fun (n, ci) =>
    ci matches .defnInfo _ && modOf n == `Claims.Assumptions && !n.isInternal && !eqn n
  for (a, _) in asms do
    let doc := (← findDocString? env a).getD ""
    let tag := match doc.splitOn "(claims_spec:" with | _ :: r :: _ => (r.splitOn ")").headD "" | _ => ""
    let cases := (tag.splitOn ",").map (·.trimAscii.toString) |>.filter (· ≠ "")
    let users := thms.filter fun (_, ci) => ci.type.getUsedConstants.contains a
    if cases.isEmpty then bad := bad.push s!"{a}: no (claims_spec: …) tag"
    if users.isEmpty then bad := bad.push s!"{a}: no theorem takes it"
    logInfo m!"assumption {a}, taken by: {users.toList.map (·.1)}"
    for c in cases do
      logInfo (.ofFormat (format s!"assumption-case claims_spec {c}"))
  unless bad.isEmpty do throwError "axioms beyond Lean's three, or an untied assumption:\n{String.intercalate "\n" bad.toList}"

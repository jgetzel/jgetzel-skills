import Lean
import LuaLean

/-! check.sh's gate: every theorem of LuaLean rests on Lean's three axioms (propext, Classical.choice, Quot.sound)
and nothing else (no sorryAx, no Lean.ofReduceBool from native_decide), and LuaLean declares no axiom. -/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let ours (n : Name) : Bool := match env.getModuleIdxFor? n with
    | some i => (`LuaLean).isPrefixOf env.header.moduleNames[i.toNat]!
    | none => false
  let core : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut n := 0
  let mut bad := #[]
  for (c, ci) in env.constants.toList do
    if !ours c then continue
    if ci matches .axiomInfo _ then bad := bad.push s!"{c}: an axiom"
    if ci matches .thmInfo _ && !c.isInternal then
      n := n + 1
      let extra := (← collectAxioms c).filter (!core.contains ·)
      unless extra.isEmpty do bad := bad.push s!"{c}: {extra.toList}"
  logInfo s!"{n} theorems rest on Lean's axioms alone"
  unless bad.isEmpty do throwError "beyond Lean's axioms:\n{String.intercalate "\n" bad.toList}"

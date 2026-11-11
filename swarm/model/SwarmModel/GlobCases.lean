import Lean.Data.Json
import SwarmModel.Glob

/-! Random lock patterns and paths, with what Glob.lean says of them, for ../lua/test/locks_model_spec.lua to check
locks.lua against (and `gm` against fnmatch on the `tame` patterns, where both read a pattern alike).
`lake env lean --run SwarmModel/GlobCases.lean <n> <seed> <fix> <file>` (replay.sh) writes
`{"cases": [{"p", "q", "x", "tok", "cov", "ov", "gm", "tame"}, ..]}`: `tok` is `tokens fix p` as the Lua's tables,
`cov` covers fix x p, `ov` overlaps fix p q, `gm` the glob semantics of p on x. -/

open Lean Swarm.Glob

def tokJson : Tok → Json
  | .star => "*" | .any => "?" | .ch c => Json.mkObj [("c", c.toString)] | .set s => Json.mkObj [("set", String.ofList s)]

abbrev G := StateM StdGen

def rnd (n : Nat) : G Nat := modifyGet fun g => randNat g 0 n
def pick (cs : String) : G Char := return cs.toList.getD (← rnd (cs.length - 1)) 'a'
def str (cs : String) (n : Nat) : G (List Char) := do
  let mut r := []
  for _ in [0:← rnd n] do r := (← pick cs) :: r
  return r

/-- any pattern: metacharacters anywhere, unbalanced brackets, escapes -/
def wild : G (List Char) := str "aabb//.*?[]!^-\\" 8
/-- a pattern fnmatch reads as we do: `*`, `?`, plain characters and classes like `[ab]`, `[!a]`, `[a-b]` -/
def tame : G (List Char) := do
  let mut r := []
  for _ in [0:← rnd 5] do
    let piece ← match ← rnd 5 with
      | 0 => pure ['*'] | 1 => pure ['?']
      | 2 => do
        let neg := if (← rnd 1) == 0 then ['!'] else []
        let lo ← pick "ab"
        let hi ← pick "bz"
        let other ← pick "ab/."
        pure (['['] ++ neg ++ [lo] ++ (if (← rnd 1) == 0 then ['-', hi] else [other]) ++ [']'])
      | _ => return [← pick "ab/."]
    r := r ++ piece
  return r

/-- a string the tokens match, mostly -/
def sample (t : List Tok) : G (List Char) := do
  let mut r := []
  for k in t do
    match k with
    | .star => r := r ++ (← str "ab/." 3)
    | .any => r := r ++ [← pick "ab/.]"]
    | .ch c => r := r ++ [c]
    | .set s =>
      let cs := "ab./]-!^z".toList.filter (inSet s)
      r := r ++ [cs.getD (← rnd (cs.length - 1)) 'a']
  return r

def case (fix : Bool) : G Json := do
  let isTame := (← rnd 1) == 0
  let p ← if isTame then tame else wild
  let q ← if (← rnd 2) == 0 then tame else wild
  let fs := forms true p
  let x ← if (← rnd 2) == 0 then str "ab/.*?[]!\\" 8 else sample (fs.getD (← rnd (fs.length - 1)) [])
  return Json.mkObj [("p", String.ofList p), ("q", String.ofList q), ("x", String.ofList x),
    ("tok", Json.arr ((tokens fix p).map tokJson).toArray), ("cov", covers fix x p), ("ov", overlaps fix p q),
    ("gm", gm (tokens true p) x), ("tame", isTame)]

def main (args : List String) : IO UInt32 := do
  let [n, seed, fix, file] := args | do IO.eprintln "usage: GlobCases.lean <n> <seed> <fix: true|false> <file>"; return 1
  let cases := (List.range n.toNat!).mapM (fun _ => case (fix == "true")) |>.run' (mkStdGen seed.toNat!)
  IO.FS.writeFile file (Json.mkObj [("cases", Json.arr cases.toArray)]).compress
  return 0

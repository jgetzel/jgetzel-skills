import Lean.Data.Json
import SwarmModel.Model

/-! Random runs of the `replay` instance as JSON, for ../lua/test/cli_model_spec.lua to replay through the CLI.
`lake env lean --run SwarmModel/Traces.lean <n> <steps> <seed> <dir>` (replay.sh) writes `<dir>/seed<seed>-<i>.json`:
`{"states": [{"s": state}, {"action": name, "picks": {..}, "s": state}, ..]}`. -/

open Lean Swarm

def slot (a : Nat) : String := s!"m-{a + 1}"
def who (o : Option Nat) : String := (o.map slot).getD ""

/-- the ids in a bitmask: how a step names a set of tasks -/
def depSet (c : Cfg) (mask : Nat) : List Nat := c.tasks.filter fun t => mask.testBit (t - 1)

def stateJson (c : Cfg) (s : State) : Json :=
  let tst : TSt → String
    | .absent => "absent" | .opn => "open" | .claimed => "claimed" | .blocked => "blocked" | .done => "done" | .dropped => "dropped"
  let ast : ASt → String
    | .unborn => "unborn" | .working => "working" | .idle => "idle" | .blocked => "blocked" | .ended => "ended"
  let kind : Kind → String | .dm => "dm" | .answer => "answer" | .released => "released" | .digest => "digest"
  Json.mkObj [
    ("task", Json.arr <| s.task.toArray.map fun k => Json.mkObj
      [("st", tst k.st), ("owner", who k.owner), ("lease", k.lease), ("ev", k.ev), ("answer", k.answer)]),
    ("ag", Json.mkObj <| c.agents.map fun a => (slot a, Json.mkObj [("st", ast (s.agt a).st), ("boot", (s.agt a).boot)])),
    ("lock", Json.mkObj <| (c.patterns.zip s.lock).map fun (p, l) => (p, Json.mkObj [("holder", who l.holder)])),
    ("log", Json.arr <| s.log.toArray.map fun m => Json.mkObj
      [("frm", who m.frm), ("to", slot m.to), ("urgent", m.urgent), ("kind", kind m.kind)]),
    ("cursor", Json.mkObj <| c.agents.map fun a => (slot a, s.cur a))]

abbrev Step := String × List (String × Json) × Option State

/-- every action with every argument, in four groups: the agents' commands, the environment, the communicator,
watchd. -/
def steps (c : Cfg) (s : State) : List (List Step) :=
  let ags := c.agents
  let ts := c.tasks
  let ps := List.range c.patterns.length
  let bs : List Bool := [true, false]
  let a (k : String) (x : Nat) : String × Json := (k, slot x)
  let n (k : String) (x : Nat) : String × Json := (k, x)
  let p (k : String) (x : Nat) : String × Json := (k, c.pat x)
  let d (k : String) (m : Nat) : String × Json := (k, toJson (depSet c m))
  let masks := List.range (2 ^ c.ntasks)
  [ ags.flatMap fun x =>
      (ts.flatMap fun t => [
        ("claim", [a "a1" x, n "t1" t], claim c s x t),
        ("renew", [a "a4" x, n "t4" t], renew s x t),
        ("release", [a "a5" x, n "t5" t], release s x t),
        ("block", [a "a6" x, n "t6" t], block s x t),
        ("dropOwn", [a "a8" x, n "t8" t], dropOwn s x t)]
        ++ bs.map fun ev => ("done", [a "a7" x, n "t7" t, ("ev7", toJson ev)], done c s x t ev))
      ++ (ps.flatMap fun q => [
        ("lock", [a "a9" x, p "p9" q], lock c s x q),
        ("unlock", [a "a10" x, p "p10" q], unlock s x q)])
      ++ (ags.flatMap fun y => bs.map fun u => ("postTo", [a "a11" x, a "b11" y, ("u11", toJson u)], postTo s x y u))
      ++ [("readAll", [a "a12" x], readAll s x)]
      ++ bs.map fun big => ("stop", [a "a14" x, ("big14", toJson big)], stop c s x big),
    (ags.flatMap fun x => [
        ("wake", [a "a15" x], wake c s x),
        ("prompt", [a "a18" x], prompt s x),
        ("boot", [a "a19" x], boot c s x),
        ("waiterGone", [a "a20" x], waiterGone s x),
        ("age", [a "a21" x], age s x),
        ("cool", [a "a22" x], cool s x)])
      ++ (ts.map fun t => ("expire", [n "t23" t], expire s t))
      ++ ps.map fun q => ("expireLock", [p "p24" q], expireLock s q),
    (masks.map fun m => ("add", [d "d28" m], add s (depSet c m)))
      ++ (ts.flatMap fun t => masks.map fun m => ("after", [n "t29" t, d "d29" m], after c s t (depSet c m)))
      ++ ts.flatMap fun t => [("unblock", [n "t30" t], unblock c s t), ("drop", [n "t31" t], drop s t)],
    [("tick", [], tick c s)] ]

def run (c : Cfg) (maxSteps : Nat) (g : StdGen) : Json := Id.run do
  let mut s := init c
  let mut g := g
  let mut out := #[Json.mkObj [("s", stateJson c s)]]
  for _ in [0:maxSteps] do
    -- the agents' group is never empty: a dead end there (no live agent) still leaves the rest
    let groups := ((steps c s).map fun grp => grp.filterMap fun (name, picks, r) => r.map (name, picks, ·)).filter (!·.isEmpty)
    if groups.isEmpty then break
    -- a group (the agents' twice), then one of its enabled actions, then its arguments: each evenly
    let groups := groups.take 1 ++ groups
    let (i, g1) := randNat g 0 (groups.length - 1)
    let names := ((groups.getD i []).map (·.1)).eraseDups
    let (k, g2) := randNat g1 0 (names.length - 1)
    let grp := (groups.getD i []).filter (·.1 == names.getD k "")
    let (j, g3) := randNat g2 0 (grp.length - 1)
    g := g3
    if let some (name, picks, s') := grp[j]? then
      s := s'
      out := out.push (Json.mkObj [("action", name), ("picks", Json.mkObj picks), ("s", stateJson c s)])
  return Json.mkObj [("states", Json.arr out)]

def main (args : List String) : IO UInt32 := do
  let [n, maxSteps, seed, dir] := args | do IO.eprintln "usage: Traces.lean <n> <steps> <seed> <dir>"; return 1
  let seed := seed.toNat!
  for i in [0:n.toNat!] do
    IO.FS.writeFile (System.FilePath.mk dir / s!"seed{seed}-{i}.json") (run replay maxSteps.toNat! (mkStdGen (seed * 1000 + i))).compress
  return 0

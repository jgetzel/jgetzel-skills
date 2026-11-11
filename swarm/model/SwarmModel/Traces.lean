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
  let kind : Kind → String | .dm => "dm" | .answer => "answer" | .released => "released" | .digest => "digest" | .nudge => "nudge"
  Json.mkObj [
    ("task", Json.arr <| (s.task.toArray.mapIdx fun i k => (i + 1, k)).map fun (t, k) => Json.mkObj
      [("base", c.tbase t), ("st", tst k.st), ("owner", who k.owner), ("lease", k.lease), ("ev", k.ev), ("answer", k.answer)]),
    ("ag", Json.mkObj <| c.agents.map fun a => (slot a, Json.mkObj [("st", ast (s.agt a).st), ("boot", (s.agt a).boot),
      ("wt", ((s.agt a).wt.map toJson).getD (-1 : Int))])),
    ("lock", Json.mkObj <| (c.patterns.zip s.lock).map fun (p, l) => (p, Json.mkObj [("holder", who l.holder)])),
    ("log", Json.arr <| s.log.toArray.map fun m => Json.mkObj
      [("frm", who m.frm), ("to", slot m.to), ("urgent", m.urgent), ("kind", kind m.kind)]),
    ("cursor", Json.mkObj <| c.agents.map fun a => (slot a, s.cur a)),
    ("wts", Json.arr <| c.wtIds.toArray.map fun w => let x := s.git.wt w; Json.mkObj
      [("on", x.on), ("br", (x.br.map toJson).getD (-1 : Int)), ("head", x.head), ("dirty", x.dirty), ("recent", x.recent)]),
    ("brs", Json.arr <| (List.range (c.nbases + c.nwts)).toArray.map fun b => ((s.git.tip b).map toJson).getD (-1 : Int))]

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
        -- 4000 s idle is also 30 min: watchd's tick would nudge an agent its unclean worktree keeps (the model's `nudge`)
        ("cool", [a "a22" x], if unlanded c s x then none else cool s x)])
      ++ (ts.map fun t => ("expire", [n "t23" t], expire c s t))
      ++ ps.map fun q => ("expireLock", [p "p24" q], expireLock s q),
    (masks.map fun m => ("add", [d "d28" m], add s (depSet c m)))
      ++ (ts.flatMap fun t => masks.map fun m => ("after", [n "t29" t, d "d29" m], after c s t (depSet c m)))
      ++ ts.flatMap fun t => [("unblock", [n "t30" t], unblock c s t), ("drop", [n "t31" t], drop s t)],
    [("tick", [], tick c s)],
    -- the agents' git commands, and the world in a worktree
    (ags.flatMap fun x => c.wtIds.flatMap fun w =>
      let g (op : GitOp) := gitCmd c s x op
      [("gitAdd", [a "a40" x, n "w40" w], g (.add w)), ("gitEdit", [a "a41" x, n "w41" w], g (.edit w)),
        ("gitCommit", [a "a42" x, n "w42" w], g (.commit w))]
      ++ (List.range c.nbases).flatMap (fun b => [("gitLand", [a "a43" x, n "w43" w, n "r43" b], g (.land w b)),
        ("gitSquash", [a "a44" x, n "w44" w, n "r44" b], g (.squash w b))])
      ++ (List.range (c.nbases + c.nwts)).map fun b => ("gitCheckout", [a "a45" x, n "w45" w, n "r45" b], g (.checkout w b)))
      ++ c.wtIds.flatMap fun w => [("wtAge", [n "w46" w], world s w .age)]
        ++ bs.map fun v => ("wtProc", [n "w47" w, ("v47", toJson v)], world s w (.proc v)) ]

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

/-- a run given as steps' names and picks: each must be enabled -/
def script (c : Cfg) (acts : List (String × List (String × Json))) : Except String Json := do
  let mut s := init c
  let mut out := #[Json.mkObj [("s", stateJson c s)]]
  for (name, picks) in acts do
    match (steps c s).flatten.filter (fun (n, p, _) => n == name && p == picks) with
    | [(_, _, some s')] =>
      s := s'
      out := out.push (Json.mkObj [("action", name), ("picks", Json.mkObj picks), ("s", stateJson c s)])
    | _ => throw s!"step {out.size}: {name} {(Json.mkObj picks).compress} is not enabled"
  return Json.mkObj [("states", Json.arr out)]

namespace S
def ag (k : String) (x : Nat) : String × Json := (k, slot x)
def gAdd (x w : Nat) := ("gitAdd", [ag "a40" x, ("w40", toJson w)])
def gEdit (x w : Nat) := ("gitEdit", [ag "a41" x, ("w41", toJson w)])
def gCommit (x w : Nat) := ("gitCommit", [ag "a42" x, ("w42", toJson w)])
def gLand (x w b : Nat) := ("gitLand", [ag "a43" x, ("w43", toJson w), ("r43", toJson b)])
def gSquash (x w b : Nat) := ("gitSquash", [ag "a44" x, ("w44", toJson w), ("r44", toJson b)])
def gCheckout (x w b : Nat) := ("gitCheckout", [ag "a45" x, ("w45", toJson w), ("r45", toJson b)])
def wAge (w : Nat) := ("wtAge", [("w46", toJson w)])
def stop (x : Nat) := ("stop", [ag "a14" x, ("big14", toJson false)])
def stopBig (x : Nat) := ("stop", [ag "a14" x, ("big14", toJson true)])
def expire (t : Nat) := ("expire", [("t23", toJson t)])
def age (x : Nat) := ("age", [ag "a21" x])
def add : String × List (String × Json) := ("add", [("d28", toJson ([] : List Nat))])
def claim (x t : Nat) := ("claim", [ag "a1" x, ("t1", toJson t)])
def done (x t : Nat) := ("done", [ag "a7" x, ("t7", toJson t), ("ev7", toJson true)])
def tick : String × List (String × Json) := ("tick", [])
end S
open S in
/-- what random runs rarely reach: worktrees removed with work on them that landed. `end`: a squash-merged worktree
is landed by content, so lifecycle ends its agent (the terminal only), and the sweep removes the worktree and its branch; a dirty one keeps its
agent. `sweep`: a fast-forwarded worktree its agent no longer edits in is swept with its branch, and so is one with the
base `formal` checked out, and the branch `formal` stays (`splitGC`). `formal` (W3, board #2): work landed on `formal` only is
not landed for the Lua: the tick sweeps a worktree on main, keeps one on `formal` its agent left (W3's orphan), and keeps
the idle agent whose last worktree is on `formal`. `base` (board #3): task #2 is on `formal`; its agent lands on main
only and goes idle (big context, so never reusable), and the tick, which reaps the idle agent 1's lapsed #1, keeps it; once the work is on `formal` too, the tick ends it. -/
def scripts : List (String × List (String × List (String × Json))) := [
  ("end", [gAdd 0 0, gEdit 0 0, gCommit 0 0, gSquash 0 0 0, gAdd 1 1, gEdit 1 1, stop 0, stop 1, age 0, age 1, tick]),
  ("sweep", [gAdd 0 0, gEdit 0 0, gCommit 0 0, gLand 0 0 0, gAdd 0 1, gEdit 0 1, wAge 0, tick,
    gAdd 1 2, gCheckout 1 2 1, wAge 2, tick]),
  ("base", [add, add, claim 1 1, claim 0 2, gAdd 0 0, gEdit 0 0, gCommit 0 0, gLand 0 0 0, done 0 2, stopBig 0, age 0, stop 1, expire 1, tick]),
  ("formal", [gAdd 0 0, gEdit 0 0, gCommit 0 0, gLand 0 0 0, gAdd 0 2, gEdit 0 2, gCommit 0 2, gSquash 0 2 1,
    gAdd 0 1, gEdit 0 1, gCommit 0 1, gSquash 0 1 1, wAge 0, wAge 2, stop 0, age 0, tick])]

def main (args : List String) : IO UInt32 := do
  if let ["script", dir] := args then
    for (name, acts) in scripts do
      match script replay acts with
      | .ok j => IO.FS.writeFile (System.FilePath.mk dir / s!"script-{name}.json") j.compress
      | .error e => do IO.eprintln s!"script {name}: {e}"; return 1
    return 0
  let [n, maxSteps, seed, dir] := args | do IO.eprintln "usage: Traces.lean <n> <steps> <seed> <dir> | script <dir>"; return 1
  let seed := seed.toNat!
  for i in [0:n.toNat!] do
    IO.FS.writeFile (System.FilePath.mk dir / s!"seed{seed}-{i}.json") (run replay maxSteps.toNat! (mkStdGen (seed * 1000 + i))).compress
  return 0

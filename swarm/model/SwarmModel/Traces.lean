import Lean.Data.Json
import SwarmModel.Spawn
import SwarmModel.PrWatch
import SwarmModel.Restart

/-! Random runs of the `sreplay` instance (`replay` with auto-spawn's launch failures, Spawn.lean) as JSON, for
../lua/test/cli_model_spec.lua to replay through the CLI.
`lake env lean --run SwarmModel/Traces.lean <n> <steps> <seed> <dir>` (replay.sh) writes `<dir>/seed<seed>-<i>.json`:
`{"states": [{"s": state}, {"action": name, "picks": {..}, "s": state}, ..]}`; a state has auto-spawn's meta rows as
`spawn`. -/

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
  let kind : Kind → String
    | .dm => "dm" | .answer => "answer" | .released => "released" | .digest => "digest" | .nudge => "nudge" | .check => "check"
  Json.mkObj [
    ("task", Json.arr <| (s.task.toArray.mapIdx fun i k => (i + 1, k)).map fun (t, k) => Json.mkObj
      [("base", c.tbase t), ("st", tst k.st), ("owner", who k.owner), ("lease", k.lease), ("ev", k.ev), ("answer", k.answer)]),
    ("ag", Json.mkObj <| c.agents.map fun a => (slot a, Json.mkObj [("st", ast (s.agt a).st), ("boot", (s.agt a).boot),
      ("wt", ((s.agt a).wt.map toJson).getD (-1 : Int)), ("stay", (s.agt a).stay)])),
    ("lock", Json.mkObj <| (c.patterns.zip s.lock).map fun (p, l) => (p, Json.mkObj [("holder", who l.holder)])),
    ("log", Json.arr <| s.log.toArray.map fun m => Json.mkObj
      [("frm", who m.frm), ("to", slot m.to), ("urgent", m.urgent), ("kind", kind m.kind)]),
    ("cursor", Json.mkObj <| c.agents.map fun a => (slot a, s.cur a)),
    ("wts", Json.arr <| c.wtIds.toArray.map fun w => let x := s.git.wt w; Json.mkObj
      [("on", x.on), ("br", (x.br.map toJson).getD (-1 : Int)), ("head", x.head), ("dirty", x.dirty), ("recent", x.recent)]),
    ("brs", Json.arr <| (List.range (c.nbases + c.nwts)).toArray.map fun b => ((s.git.tip b).map toJson).getD (-1 : Int)),
    -- board #47: what the communicator is sent and has read, the away flag, and `--back`'s digest
    ("comms", Json.arr <| s.cbox.toArray.map fun n => Json.mkObj [("kind", match n.kind with
      | .blocked => "blocked" | .away => "away" | .back => "back" | .hung => "hung"), ("task", n.task), ("urgent", n.urgent), ("qs", toJson n.qs)]),
    ("ccur", s.ccur), ("away", s.away.isSome),
    ("digest", match s.digest with
      | some g => Json.mkObj [("qs", toJson g.qs), ("done", toJson g.done), ("ended", toJson (g.ended.map slot)),
        ("hung", toJson (g.hung.map slot))]
      | none => Json.null)]

def worldJson (c : SCfg) (w : SWorld) : Json :=
  match stateJson c.sw w.s with
  | .obj kv => .obj (kv.insert "spawn" (Json.mkObj [("backoff", w.backoff), ("bo", w.bo.isSome),
      ("fails", toJson [w.fails.1, w.fails.2]), ("halt", w.halt.getD 0)]))
  | j => j

abbrev Step := String × List (String × Json) × Option State
abbrev SStep := String × List (String × Json) × Option SWorld

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
      ++ (bs.map fun on => ("stay", [a "a50" x, ("on50", toJson on)], stay s x on))
      ++ bs.map fun big => ("stop", [a "a14" x, ("big14", toJson big)], stop c s x big),
    (ags.flatMap fun x => [
        ("wake", [a "a15" x], wake c s x),
        ("prompt", [a "a18" x], prompt s x),
        ("hnudge", [a "a48" x], hnudge c s x),
        ("boot", [a "a19" x], boot c s x),
        ("waiterGone", [a "a20" x], waiterGone s x),
        ("age", [a "a21" x], age s x),
        -- 4000 s idle is also 30 min: watchd's tick would nudge an agent its unclean worktree keeps (the model's `nudge`)
        ("cool", [a "a22" x], if unlanded c s x || (s.agt x).stay then none else cool s x),
        -- watchd's liveness check (board #79). The replay moves last_active back and runs a tick, so these come only
        -- where the model's tick changes nothing; 30 min idle only for a stayer (watchd's tick would nudge another one
        -- its unclean worktree keeps), and 50 min would also check a cold one (`cool` is not for stayers)
        ("stale", [a "a52" x], if (s.agt x).stay then stale s x else none),
        ("stayCheck", [a "a53" x], if tickOf c s == s then stayCheck c s x else none),
        ("stayHung", [a "a54" x], if tickOf c s == s then stayHung c s x else none)])
      ++ (ts.map fun t => ("expire", [n "t23" t], expire c s t))
      ++ ps.map fun q => ("expireLock", [p "p24" q], expireLock s q),
    (masks.map fun m => ("add", [d "d28" m], add s (depSet c m)))
      ++ (ts.flatMap fun t => masks.map fun m => ("after", [n "t29" t, d "d29" m], after c s t (depSet c m)))
      ++ (ts.flatMap fun t => [("unblock", [n "t30" t], unblock c s t), ("drop", [n "t31" t], drop s t),
        ("releaseOther", [n "t32" t], releaseOther c s t)])
      ++ [("awayOn", [], awayOn s), ("back", [], back c s), ("commsRead", [], commsRead s)]
      -- an idle stayer 30 min idle and unclean, its stay ended, is one watchd's tick would nudge
      ++ (ags.map fun x => ("endStay", [a "a51" x], if (s.agt x).stale && unlanded c s x then none else endStay s x))
      ++ ags.flatMap fun x => bs.map fun f => ("endOther", [a "a33" x, ("f33", toJson f)], endOther c s x f),
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

/-- the model's steps, its tick watchd's (launches working), and the tick whose first launch fails: launch.sh exits
non-zero (`failExit`) or launch_agent raises before it (`failRaise`); and the backoff's time passing -/
def ssteps (c : SCfg) (w : SWorld) : List (List SStep) :=
  (steps c.sw w.s).map (·.map fun (n, p, r) => if n == "tick" then (n, p, sstep c w .tick) else (n, p, r.map ({ w with s := · })))
    |>.modify 3 (· ++ [("failExit", [], sstep c w (.fail false)), ("failRaise", [], sstep c w (.fail true)),
      ("lapse", [], sstep c w .lapse)])

def run (c : SCfg) (maxSteps : Nat) (g : StdGen) : Json := Id.run do
  let mut s := sinit c
  let mut g := g
  let mut out := #[Json.mkObj [("s", worldJson c s)]]
  for _ in [0:maxSteps] do
    -- the agents' group is never empty: a dead end there (no live agent) still leaves the rest
    let groups := ((ssteps c s).map fun grp => grp.filterMap fun (name, picks, r) => r.map (name, picks, ·)).filter (!·.isEmpty)
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
      out := out.push (Json.mkObj [("action", name), ("picks", Json.mkObj picks), ("s", worldJson c s)])
  return Json.mkObj [("states", Json.arr out)]

/-- a run given as steps' names and picks: each must be enabled -/
def script (c : SCfg) (acts : List (String × List (String × Json))) : Except String Json := do
  let mut s := sinit c
  let mut out := #[Json.mkObj [("s", worldJson c s)]]
  for (name, picks) in acts do
    match (ssteps c s).flatten.filter (fun (n, p, _) => n == name && p == picks) with
    | [(_, _, some s')] =>
      s := s'
      out := out.push (Json.mkObj [("action", name), ("picks", Json.mkObj picks), ("s", worldJson c s)])
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
def boot (x : Nat) := ("boot", [ag "a19" x])
def block (x t : Nat) := ("block", [ag "a6" x, ("t6", toJson t)])
def readAll (x : Nat) := ("readAll", [ag "a12" x])
def releaseOther (t : Nat) := ("releaseOther", [("t32", toJson t)])
def endOther (x : Nat) (f : Bool) := ("endOther", [ag "a33" x, ("f33", toJson f)])
def failExit : String × List (String × Json) := ("failExit", [])
def failRaise : String × List (String × Json) := ("failRaise", [])
def lapse : String × List (String × Json) := ("lapse", [])
def unblock (t : Nat) := ("unblock", [("t30", toJson t)])
def awayOn : String × List (String × Json) := ("awayOn", [])
def back : String × List (String × Json) := ("back", [])
def commsRead : String × List (String × Json) := ("commsRead", [])
def hnudge (x : Nat) := ("hnudge", [ag "a48" x])
def stay (x : Nat) (on : Bool) := ("stay", [ag "a50" x, ("on50", toJson on)])
def endStay (x : Nat) := ("endStay", [ag "a51" x])
def stale (x : Nat) := ("stale", [ag "a52" x])
def stayCheck (x : Nat) := ("stayCheck", [ag "a53" x])
def stayHung (x : Nat) := ("stayHung", [ag "a54" x])
end S
open S in
/-- what random runs rarely reach: worktrees removed with work on them that landed. `end`: a squash-merged worktree
is landed by content, so lifecycle ends its agent (the terminal only), and the sweep removes the worktree and its branch; a dirty one keeps its
agent. `sweep`: a fast-forwarded worktree its agent no longer edits in is swept with its branch, and a dirty one is kept (`splitGC`; an agent checking out a base is refused, `recordedWorkspaces`). `formal` (W3, board #2): the tick sweeps a worktree on main and one
whose work is on `formal` only (both reachable from a base), and keeps the idle agent whose last worktree is on `formal`
only, as it owns no task and so its base is main. `base` (board #3): task #2 is on `formal`; its agent lands on main
only and goes idle (big context, so never reusable), and the tick, which reaps the idle agent 1's lapsed #1, keeps it; once the work is on `formal` too, the tick ends it.
`spawned` (board #5): a spawned agent has the worktree spawn recorded, so a worktree it adds itself and leaves is not
the one `wt_map` picks, and the tick sweeps it while the agent works on. `added` (board #15, finding #27): a spawned agent
adds two worktrees, lands the one it last edited in and marks its task done; the other holds an uncommitted file, so the
tick that ends idle agent 1 keeps it (`ownAdded`). `retry` (board #16): the tick's launch fails, auto-spawn backs off,
and once the time is past it spawns with the failed name. `raise`: the launch raises before launch.sh runs. `halt`: five
failed launches of #1 in a row halt it; once #1 is claimed the next tick lifts the halt and spawns for #2. `release`
(H2, board #45): the communicator releases #1 from agent 0 at work, who is sent an urgent stop; no one may claim #1 until
agent 0 reads it (board #53: before, agent 1 claimed it at once, finding `not_S1_humanRelease`); agent 0 reads it, agent 1
claims #1, agent 0 claims #2, blocks on it, and the communicator releases
the blocked #2. `end-user` (H1, board #46): agent 1 claims #1 and works, agent 0 stops holding nothing; the communicator
ends agent 0 (`swarm end`, its checks pass), then agent 1 with `--force` (#1 is open again), and the tick spawns for #1.
`away` (board #47): agent 0 blocks #1 and the tick tells the communicator (urgent), who reads it; the answer comes and agent
0 asks the same question again, which the tick tells again (finding #35); the user goes away; agent 1 blocks #2, #1 is
answered and agent 0 finishes it, the tick tells #2 not urgent; agent 0 goes idle (big) and the tick ends it and spawns
for #3; `--back`: the digest has #2, #1 done and agent 0 ended, and the communicator is sent one urgent message naming #2.
`nudge` (N1', board #50): `swarm nudge` of a working agent, of the agent spawned into an ended slot, of it blocked, and
of an idle one: each changes nothing in the db but its event, and types the line into that agent's terminal only.
`stay` (board #79): the user goes away; agent 0 stays, ends its stay and stays again, agent 1 stays; both stop and idle
50 min, watchd sends each the liveness check and neither answers, so the communicator is told each hung (urgent); the
communicator ends agent 0's stay, and the tick ends it while it keeps the stayer agent 1; `--back`'s digest has agent 0
ended and agent 1 hung. -/
def scripts : List (String × List (String × List (String × Json))) := [
  ("end", [gAdd 0 0, gEdit 0 0, gCommit 0 0, gSquash 0 0 0, gAdd 1 1, gEdit 1 1, stop 0, stop 1, age 0, age 1, tick]),
  ("sweep", [gAdd 0 0, gEdit 0 0, gCommit 0 0, gLand 0 0 0, gAdd 0 1, gEdit 0 1, wAge 0, tick]),
  ("base", [add, add, claim 1 1, claim 0 2, gAdd 0 0, gEdit 0 0, gCommit 0 0, gLand 0 0 0, done 0 2, stopBig 0, age 0, stop 1, expire 1, tick]),
  ("formal", [gAdd 0 0, gEdit 0 0, gCommit 0 0, gLand 0 0 0, gAdd 0 2, gEdit 0 2, gCommit 0 2, gSquash 0 2 1,
    gAdd 0 1, gEdit 0 1, gCommit 0 1, gSquash 0 1 1, wAge 0, wAge 2, stop 0, age 0, tick]),
  ("spawned", [stop 0, age 0, tick, add, tick, boot 0, gAdd 0 0, wAge 0, tick]),
  ("added", [stop 0, age 0, tick, add, tick, boot 0, gAdd 0 0, gEdit 0 0, gAdd 0 1, gEdit 0 1, gEdit 0 0, gCommit 0 0,
    gLand 0 0 0, done 0 1, stop 0, age 0, stop 1, age 1, tick]),
  ("retry", [stop 0, age 0, tick, add, failExit, lapse, tick, boot 0]),
  ("raise", [stop 0, age 0, tick, add, failRaise, lapse]),
  ("halt", [stop 0, age 0, tick, add, failExit, lapse, failExit, lapse, failExit, lapse, failExit, lapse, failExit,
    add, claim 1 1, tick]),
  ("release", [add, add, claim 0 1, releaseOther 1, readAll 0, claim 1 1, claim 0 2, block 0 2, releaseOther 2, readAll 0]),
  ("end-user", [add, claim 1 1, stop 0, endOther 0 false, endOther 1 true, tick, boot 0]),
  ("away", [add, add, add, claim 0 1, block 0 1, tick, commsRead, unblock 1, readAll 0, block 0 1, tick, awayOn, claim 1 2,
    block 1 2, unblock 1, readAll 0, done 0 1, tick, stopBig 0, age 0, tick, back, commsRead]),
  ("nudge", [stop 0, age 0, tick, hnudge 1, add, tick, hnudge 0, boot 0, block 0 1, hnudge 0, stop 1, hnudge 1]),
  ("stay", [awayOn, stay 0 true, stay 0 false, stay 0 true, stay 1 true, stop 0, stop 1, age 0, age 1, stale 0, stale 1,
    stayCheck 0, stayCheck 1, stayHung 0, stayHung 1, endStay 0, tick, back, commsRead])]

-- ---------- PrWatch.lean's layer (board #28) ----------
namespace P
open Swarm.PrW

def worldJson (w : PWorld) : Json :=
  Json.mkObj [
    ("task", Json.arr (w.task.toArray.map fun k => Json.mkObj [
      ("st", match k.st with | .opn => "open" | .claimed => "claimed" | .done => "done"),
      ("owner", if k.st == .opn then "" else slot k.owner),
      ("pr", Json.mkObj [("opened", k.pr.opened), ("checks", k.pr.checks.name), ("merged", k.pr.merged), ("told", k.pr.told)])])),
    ("ag", Json.arr (w.ag.toArray.map fun g => Json.mkObj [("working", g.working), ("stays", g.stays), ("urgent", g.urgent)]))]

/-- an action as its name and picks: agents as slot names, tasks as their ids from 1 -/
def actJson : PAction → String × Json
  | .claim a t => ("claim", Json.mkObj [("a", slot a), ("t", toJson (t + 1))])
  | .openPr a t => ("openPr", Json.mkObj [("a", slot a), ("t", toJson (t + 1))])
  | .push a t => ("push", Json.mkObj [("a", slot a), ("t", toJson (t + 1))])
  | .stay a v => ("stay", Json.mkObj [("a", slot a), ("v", v)])
  | .stop a => ("stop", Json.mkObj [("a", slot a)])
  | .read a => ("read", Json.mkObj [("a", slot a)])
  | .merge a t => ("merge", Json.mkObj [("a", slot a), ("t", toJson (t + 1))])
  | .done a t => ("done", Json.mkObj [("a", slot a), ("t", toJson (t + 1))])
  | .finish t ok => ("finish", Json.mkObj [("t", toJson (t + 1)), ("ok", ok)])
  | .poll => ("poll", Json.mkObj [])
  | .wake a => ("wake", Json.mkObj [("a", slot a)])

/-- a run of the layer, each step enabled: `{"pr": {"gated"}, "states": [{"s"}, {"action", "picks", "s"}, ..]}` -/
def script (c : PCfg) (acts : List PAction) : Except String Json := do
  let mut w := pinit c
  let mut out := #[Json.mkObj [("s", worldJson w)]]
  for x in acts do
    match pstep c w x with
    | some w' =>
      w := w'
      let (n, p) := actJson x
      out := out.push (Json.mkObj [("action", n), ("picks", p), ("s", worldJson w)])
    | none => throw s!"step {out.size}: {(actJson x).1} is not enabled"
  return Json.mkObj [("pr", Json.mkObj [("gated", c.gated)]), ("states", Json.arr out)]

/-- `pr-green`: the stall of finding #30 (an agent stays idle for its PR's checks; CI goes green), then the fix: the poll
wakes it, it merges, and the next poll marks the task done. `pr-red`: the checks fail, the poll wakes it once for that
head, it pushes and stops, the poll says nothing while the new head's checks run, they go green and the poll wakes it
again. `pr-merged` (finding #31, a repo that isn't pr-gated): the owner merges, stays and stops with the task claimed;
the poll marks it done and wakes it, and its green checks wake no one. -/
def scripts : List (String × PCfg × List PAction) := [
  ("pr-green", { gated := true }, [.claim 0 0, .openPr 0 0, .stay 0 true, .stop 0, .finish 0 true, .poll, .wake 0,
    .merge 0 0, .poll, .read 0, .stay 0 false]),
  ("pr-red", { gated := true }, [.claim 0 0, .openPr 0 0, .stay 0 true, .stop 0, .finish 0 false, .poll, .poll, .wake 0,
    .push 0 0, .stop 0, .poll, .finish 0 true, .poll, .wake 0]),
  ("pr-merged", {}, [.claim 0 0, .openPr 0 0, .finish 0 true, .merge 0 0, .stay 0 true, .stop 0, .poll, .wake 0, .poll])]
end P

-- ---------- Restart.lean's layer (board #49): one swarm's watchd record, watchd_up and processes ----------
namespace R

def pid (o : Option Nat) : Json := (o.map toJson).getD Json.null

def worldJson (w : World) : Json :=
  Json.mkObj [("rec", pid (w.wdOf 0)), ("up", pid (w.upOf 0)), ("tk", pid (w.tkOf 0)), ("restart", (w.rsOf 0).isSome),
    ("wds", Json.arr ((List.range w.wds.length).toArray.map fun p =>
      Json.mkObj [("term", (w.proc p).term), ("alive", w.alive p)]))]

/-- an action as its name and picks: terminals and watchds by the model's numbers -/
def actJson : CAction → String × Json
  | .open sp => ("open", Json.mkObj [("sp", sp)])
  | .watchd i x => ("watchd", Json.mkObj [("i", i), ("x", x)])
  | .tick i => ("tick", Json.mkObj [("i", i)])
  | .restart i x => ("restart", Json.mkObj [("i", i), ("x", x)])
  | .takeover p => ("takeover", Json.mkObj [("p", p)])
  | .crash p => ("crash", Json.mkObj [("p", p)])
  | .loop p => ("loop", Json.mkObj [("p", p)])
  | .rpoll i => ("rpoll", Json.mkObj [("i", i)])
  | .rok i => ("rok", Json.mkObj [("i", i)])
  | .rfail i => ("rfail", Json.mkObj [("i", i)])
  | .tend p => ("tend", Json.mkObj [("p", p)])
  | a => (s!"{repr a}", Json.mkObj [])

/-- a run of one swarm, each step enabled: `{"restart": {}, "states": [{"s"}, {"action", "picks", "s"}, ..]}` -/
def script (c : CCfg) (acts : List CAction) : Except String Json := do
  let mut w := cinit c
  let mut out := #[Json.mkObj [("s", worldJson w)]]
  for x in acts do
    match cstep c w x with
    | some w' =>
      w := w'
      let (n, p) := actJson x
      out := out.push (Json.mkObj [("action", n), ("picks", p), ("s", worldJson w)])
    | none => throw s!"step {out.size}: {(actJson x).1} is not enabled"
  return Json.mkObj [("restart", Json.mkObj []), ("states", Json.arr out)]

/-- one swarm with nothing to tick but the watchds, and board #41's handover (the Lua's) -/
def cfg : CCfg := { sw := { nagents := 0, roster := 0, ntasks := 0 }, nswarms := 1, home := [0], waitUp := true }

/-- `restart-ok`: watchd 0, started by hand, ticks; `--restart` starts watchd 1, which takes the record while watchd 0 is
mid-tick; the restart's poll sees it; watchd 0's tick ends (board #71: until then watchd 1's waits); watchd 1 ticks; the
restart reports success and watchd 0's loop exits. `restart-dies`: watchd 1 takes the record and dies before its first
tick; watchd 0's tick ends and its loop takes the record back; the restart reports the failure. -/
def scripts : List (String × CCfg × List CAction) := [
  ("restart-ok", cfg, [.open 0, .watchd 0 0, .tick 0, .open 0, .restart 0 1, .takeover 1, .rpoll 0, .tend 0, .tick 0,
    .rok 0, .loop 0]),
  ("restart-dies", cfg, [.open 0, .watchd 0 0, .tick 0, .open 0, .restart 0 1, .takeover 1, .rpoll 0, .crash 1, .tend 0,
    .loop 0, .rfail 0])]
end R

def main (args : List String) : IO UInt32 := do
  if let ["script", dir] := args then
    for (name, acts) in scripts do
      match script sreplay acts with
      | .ok j => IO.FS.writeFile (System.FilePath.mk dir / s!"script-{name}.json") j.compress
      | .error e => do IO.eprintln s!"script {name}: {e}"; return 1
    for (name, c, acts) in P.scripts do
      match P.script c acts with
      | .ok j => IO.FS.writeFile (System.FilePath.mk dir / s!"script-{name}.json") j.compress
      | .error e => do IO.eprintln s!"script {name}: {e}"; return 1
    for (name, c, acts) in R.scripts do
      match R.script c acts with
      | .ok j => IO.FS.writeFile (System.FilePath.mk dir / s!"script-{name}.json") j.compress
      | .error e => do IO.eprintln s!"script {name}: {e}"; return 1
    return 0
  let [n, maxSteps, seed, dir] := args | do IO.eprintln "usage: Traces.lean <n> <steps> <seed> <dir> | script <dir>"; return 1
  let seed := seed.toNat!
  for i in [0:n.toNat!] do
    IO.FS.writeFile (System.FilePath.mk dir / s!"seed{seed}-{i}.json") (run sreplay maxSteps.toNat! (mkStdGen (seed * 1000 + i))).compress
  return 0

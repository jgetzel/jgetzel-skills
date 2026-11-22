import Tests.Cli.Fixture

/-! cli_comms_spec.lua: ensureComms (model Comms.lean, findings #22 to #24) and the machine's swarms (sw-global §2):
join labels a terminal with its swarm and refuses one of another swarm without --takeover; a communicator `<x>-comms`
in no swarm makes swarm `x`; with two live swarms a command must be told which; watchd launches a missing communicator
and holds auto-spawn when it can't. -/

namespace SwarmLean.Tests.Cli.Comms
open SwarmLean.Tests.Cli
open Lean (Json toJson)

/-- hc: ls from hc.json, get <t> prints labels from label.<t>.json, label <t> k=v writes swarm.comms. -/
def setup (t : T) (terms : List Json) (labels : List (String × Json) := []) : IO Unit := do
  t.fakes
  let D := shquote t.d
  discard <| t.fake "hc" s!"#!/bin/sh\nD={D}\ncase \"$1\" in\n  ls) cat $D/hc.json; echo ;;\n  get) cat $D/label.$2.json 2>/dev/null || echo '\{}' ;;\n  label) shift; a=$1; shift; echo \"$a $*\" >> $D/labels.log ;;\n  *) echo '\{}' ;;\nesac\n"
  t.setHc terms
  for (a, l) in labels do put (t.d ++ "/label." ++ a ++ ".json") (Json.mkObj [("labels", l)]).compress
  put (← t.launch) s!"#!/bin/sh\necho \"$1\" >> {D}/launch.space\n[ -f {D}/launch.fail ] && \{ echo \"no Herdr window\" >&2; exit 1; }\necho t9\n" (some "755")

def join (t : T) (who hc : String) (flag : Option String := none) : IO R :=
  t.sw who (["join"] ++ flag.toList) { hc := some hc, ok := false }

def metaV (t : T) (k : String) : IO Json := return (← t.q1 s!"select v from meta where k='{k}'").f "v"

def test_join_labels_the_terminal_with_its_swarm (t : T) : IO Unit := do
  setup t [json% {"address": "t1"}]
  t.q_ "update swarm set comms='c' where name='t'"
  eq (← join t "c" "t1").code 0
  eq (← metaV t "comms_hc") "t1"
  eq ((← t.q1 "select swarm from agent where name='c'").f "swarm") "t"
  has (← t.calls "labels") "t1 swarm=t"

def test_join_refused_in_another_swarms_terminal (t : T) : IO Unit := do
  setup t [json% {"address": "t1"}] [("t1", json% {"swarm": "other"})]
  let r ← join t "c" "t1"
  eq (decide (r.code ≠ 0)) true
  has r.stderr "in swarm other"
  eq (← join t "c" "t1" (some "--takeover")).code 0
  has (← t.calls "labels") "t1 swarm=t"

def test_join_as_comms_makes_its_swarm (t : T) : IO Unit := do
  setup t [json% {"address": "t1"}]
  t.sw_ "zz" ["new", "u"]  -- two live swarms: none resolves for x-comms
  eq (← join t "x-comms" "t1").code 0
  eq ((← t.q1 "select swarm from agent where name='x-comms'").f "swarm") "x"
  eq ((← t.q1 "select comms from swarm where name='x'").f "comms") "x-comms"
  eq ((← t.q1 "select repo from swarm_repo where swarm='x'").f "repo") t.repo
  has (← t.calls "labels") "t1 swarm=x"
  -- three live swarms: a command of no agent must be told which
  let r ← t.sw "zz" ["board"] { ok := false }
  eq r.code 1
  has r.stderr "which swarm"
  has (← t.sw "x-comms" ["board"]).stdout ""  -- its agent row says x
  eq (← t.sw "zz" ["--swarm", "t", "board"]).code 0
  eq (← t.sw "zz" ["board"] { env := [("SWARM", some "x")] }).code 0
  has (← t.sw "zz" ["board"] { env := [("SWARM", some "nope")], ok := false }).stderr "no swarm 'nope'"
  let l := (← t.sw "zz" ["swarms"]).stdout
  has l "t  comms -"; has l "x  comms x-comms  1 live: x-comms"

def test_new_makes_a_swarm_once (t : T) : IO Unit := do
  has (← t.sw "zz" ["new", "u", "--repo", t.wt]).stdout s!"swarm u ({t.repo})"
  has (← t.sw "zz" ["new", "u"] { ok := false }).stderr "swarm u exists"
  eq ((← t.q1 "select base from repo where path=?" [.text t.repo]).f "base") "main"

def tick (t : T) : IO Unit :=
  t.sw_ "a" ["watchd", "--once", "--comms", "c", "--max-agents", "1", "--min-free-mem", "0"]

def test_watchd_launches_missing_communicator (t : T) : IO Unit := do
  setup t [json% {"address": "t3"}]
  t.agent "a" [("status", "working")]
  t.q_ "insert into meta(k,v) values('comms_hc','t0')"  -- c joined from a Herdr terminal once
  t.q_ "insert into task(title,state) values('x','open')"  -- work the swarm can start
  tick t
  has ((← slurp (t.d ++ "/launch.space")).getD "") "c"
  eq ((← t.q1 "select hc from agent where name='c'").f "hc") "t9"
  has (← t.calls "labels") "t9 swarm=t"

def test_watchd_leaves_a_good_communicator (t : T) : IO Unit := do
  setup t [json% {"address": "t1"}] [("t1", json% {"swarm": "t"})]
  t.agent "a" [("status", "working")]
  eq (← join t "c" "t1").code 0
  tick t
  eq (← slurp (t.d ++ "/launch.space")) Json.null

-- sw-global §4 (events 1376-1378: watchd took gl-comms's live binding): the communicator is present when its row is
-- bound to a live terminal, whatever that terminal's label says; watchd never moves a live binding
def test_watchd_never_moves_a_live_communicator (t : T) : IO Unit := do
  setup t [json% {"address": "t1"}] [("t1", json% {"swarm": "other"})]
  eq (← join t "c" "t1" (some "--takeover")).code 0  -- hc get still shows swarm=other: the label is not presence
  t.agent "a" [("status", "working")]
  t.q_ "insert into task(title,state) values('x','open')"
  tick t; tick t
  eq (← slurp (t.d ++ "/launch.space")) Json.null
  eq ((← t.q1 "select hc, ended from agent where name='c'").f "hc") "t1"
  eq (← t.q "select 1 from event where kind='comms-launch'").size 0

-- the bound terminal is gone and the swarm has work: a communicator is launched and bound
def test_watchd_launches_when_the_bound_terminal_is_gone (t : T) : IO Unit := do
  setup t [json% {"address": "t1"}]
  eq (← join t "c" "t1").code 0
  t.agent "a" [("status", "working")]
  t.q_ "insert into task(title,state) values('x','open')"
  tick t
  eq (← slurp (t.d ++ "/launch.space")) Json.null  -- t1 live: present
  t.setHc [json% {"address": "t3"}]
  tick t
  has ((← slurp (t.d ++ "/launch.space")).getD "") "c"
  eq ((← t.q1 "select hc from agent where name='c' and ended is null").f "hc") "t9"

-- board #67: only work this swarm can start counts: a held task, or live agents with nothing open, launch none
def test_watchd_launches_no_communicator_without_startable_work (t : T) : IO Unit := do
  setup t [json% {"address": "t3"}]
  t.agent "a" [("status", "working")]
  t.q_ "insert into meta(k,v) values('comms_hc','t0')"
  tick t
  eq (← slurp (t.d ++ "/launch.space")) Json.null
  t.q_ "insert into task(title,state,hold) values('x','open','later')"
  tick t
  eq (← slurp (t.d ++ "/launch.space")) Json.null
  t.q_ "update task set hold=null"
  tick t
  has ((← slurp (t.d ++ "/launch.space")).getD "") "c"

def test_watchd_holds_autospawn_when_comms_cant_launch (t : T) : IO Unit := do
  setup t [json% {"address": "t3"}]
  t.agent "a" [("status", "working")]
  t.q_ "insert into meta(k,v) values('comms_hc','t0')"
  t.q_ "insert into task(title,state) values('x','open')"
  put (t.d ++ "/launch.fail") ""
  tick t
  tick t  -- inside the backoff: no second launch attempt
  eq (splitlines ((← slurp (t.d ++ "/launch.space")).getD "")).length 1
  has (← metaV t "spawn_held") "no communicator can be launched"

def tests : List Case := [
  ("test_join_labels_the_terminal_with_its_swarm", test_join_labels_the_terminal_with_its_swarm),
  ("test_join_refused_in_another_swarms_terminal", test_join_refused_in_another_swarms_terminal),
  ("test_join_as_comms_makes_its_swarm", test_join_as_comms_makes_its_swarm),
  ("test_new_makes_a_swarm_once", test_new_makes_a_swarm_once),
  ("test_watchd_launches_missing_communicator", test_watchd_launches_missing_communicator),
  ("test_watchd_leaves_a_good_communicator", test_watchd_leaves_a_good_communicator),
  ("test_watchd_never_moves_a_live_communicator", test_watchd_never_moves_a_live_communicator),
  ("test_watchd_launches_when_the_bound_terminal_is_gone", test_watchd_launches_when_the_bound_terminal_is_gone),
  ("test_watchd_launches_no_communicator_without_startable_work", test_watchd_launches_no_communicator_without_startable_work),
  ("test_watchd_holds_autospawn_when_comms_cant_launch", test_watchd_holds_autospawn_when_comms_cant_launch)]

end SwarmLean.Tests.Cli.Comms

import Tests.Cli.Fixture

/-! cli_comms_spec.lua: ensureComms (model Comms.lean, findings #22 to #24): join refuses a communicator terminal outside
the swarm's space or bound to another swarm; watchd launches a missing communicator in the swarm's space and holds
auto-spawn when it can't. -/

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
  put (← t.launch) s!"#!/bin/sh\necho \"$1 space=$SWARM_SPACE\" >> {D}/launch.space\n[ -f {D}/launch.fail ] && \{ echo \"no Herdr window\" >&2; exit 1; }\necho t9\n" (some "755")

def join (t : T) (who hc : String) (flag : Option String := none) : IO R :=
  t.sw who (["join"] ++ flag.toList) { hc := some hc, ok := false }

def metaV (t : T) (k : String) : IO Json := return (← t.q1 s!"select v from meta where k='{k}'").f "v"

def test_join_records_space_and_labels (t : T) : IO Unit := do
  setup t [json% {"address": "t1"}] [("t1", json% {"herdr.space": "s1"})]
  t.q_ "insert or replace into meta(k,v) values('comms','c')"
  eq (← join t "c" "t1").code 0
  eq (← metaV t "space") "s1"
  has (← t.calls "labels") s!"t1 swarm.comms={t.db}"

def test_join_refused_outside_space_even_with_takeover (t : T) : IO Unit := do
  setup t [json% {"address": "t1"}] [("t1", json% {"herdr.space": "s2"})]
  t.q_ "insert or replace into meta(k,v) values('comms','c')"
  t.q_ "insert or replace into meta(k,v) values('space','s1')"
  for f in [none, some "--takeover"] do
    let r ← join t "c" "t1" f
    eq (decide (r.code ≠ 0)) true
    has r.stderr "space s1"

def test_join_refused_for_another_swarms_communicator (t : T) : IO Unit := do
  setup t [json% {"address": "t1"}] [("t1", json% {"herdr.space": "s1", "swarm.comms": "/other/swarm.db"})]
  t.q_ "insert or replace into meta(k,v) values('comms','c')"
  let r ← join t "c" "t1"
  eq (decide (r.code ≠ 0)) true
  has r.stderr "another swarm"
  eq (← join t "c" "t1" (some "--takeover")).code 0

def tick (t : T) : IO Unit :=
  t.sw_ "a" ["watchd", "--once", "--comms", "c", "--max-agents", "1", "--min-free-mem", "0"]

def test_watchd_launches_missing_communicator_in_space (t : T) : IO Unit := do
  setup t [json% {"address": "t3"}]
  t.agent "a" [("status", "working")]
  t.q_ "insert or replace into meta(k,v) values('space','s1')"
  tick t
  has ((← slurp (t.d ++ "/launch.space")).getD "") "c space=s1"
  eq ((← t.q1 "select hc from agent where name='c'").f "hc") "t9"
  has (← t.calls "labels") s!"t9 swarm.comms={t.db}"

def test_watchd_leaves_a_good_communicator (t : T) : IO Unit := do
  setup t [json% {"address": "t1"}] [("t1", json% {"herdr.space": "s1", "swarm.comms": $t.db})]
  t.agent "a" [("status", "working")]
  t.q_ "insert or replace into meta(k,v) values('space','s1')"
  eq (← join t "c" "t1").code 0
  tick t
  eq (← slurp (t.d ++ "/launch.space")) Json.null

def test_watchd_holds_autospawn_when_comms_cant_launch (t : T) : IO Unit := do
  setup t [json% {"address": "t3"}]
  t.agent "a" [("status", "working")]
  t.q_ "insert or replace into meta(k,v) values('space','s1')"
  t.q_ "insert into task(title,state) values('x','open')"
  put (t.d ++ "/launch.fail") ""
  tick t
  tick t  -- inside the backoff: no second launch attempt
  eq (splitlines ((← slurp (t.d ++ "/launch.space")).getD "")).length 1
  has (← metaV t "spawn_held") "no communicator can be launched"

-- SKILL.md's order: the communicator joins before anything names it, then watchd names it; its start records the space
def test_join_then_watchd_records_space (t : T) : IO Unit := do
  setup t [json% {"address": "t1"}] [("t1", json% {"herdr.space": "s1"})]
  eq (← join t "c" "t1").code 0
  eq (← metaV t "space") Json.null
  tick t
  eq (← metaV t "space") "s1"
  has (← t.calls "labels") s!"t1 swarm.comms={t.db}"

def test_watchd_start_leaves_another_swarms_terminal (t : T) : IO Unit := do
  setup t [json% {"address": "t1"}] [("t1", json% {"herdr.space": "s1", "swarm.comms": "/other/swarm.db"})]
  eq (← join t "c" "t1").code 0
  tick t
  eq (← metaV t "space") Json.null
  eq (← t.calls "labels") ([] : List String)

/-- `swarm state --json --view swarms`' swarms as (db, watchd). -/
def listed (t : T) : IO (List (Json × Json)) := do
  let r ← t.sw "c" ["state", "--json", "--view", "swarms"]
  let j := (Json.parse r.stdout).toOption.getD .null
  return match j.f "swarms" with | .arr a => a.toList.map fun w => (w.f "db", w.f "watchd") | _ => []

-- no watchd: a join registers the swarm while its terminal lives
def test_join_registers_without_watchd (t : T) : IO Unit := do
  setup t [json% {"address": "t1"}] [("t1", json% {"herdr.space": "s1"})]
  eq (← join t "c" "t1").code 0
  eq (← listed t) [(Json.str t.db, Json.bool false)]
  t.setHc [json% {"address": "t2"}]
  eq (← listed t) ([] : List (Json × Json))
  eq ((← System.FilePath.readDir (t.d ++ "/.state/swarm/swarms")).size) 0

-- outside a repo with SWARM_DB unset: the communicator's terminal label finds its db
def test_no_repo_label_finds_the_db (t : T) : IO Unit := do
  setup t [json% {"address": "t1"}] [("t1", json% {"herdr.space": "s1", "swarm.comms": $t.db})]
  t.q_ "insert into task(title,state) values('x','open')"
  IO.FS.createDirAll (t.d ++ "/plain")
  let r ← t.sw "c" ["board"] { hc := some "t1", cwd := some (t.d ++ "/plain"), env := [("SWARM_DB", none)] }
  has r.stdout "x"

-- with no label: the error names the swarms below the cwd, each with its SWARM_DB; machine still answers
def test_no_repo_names_the_swarms_below (t : T) : IO Unit := do
  t.fakes
  IO.FS.createDirAll (t.d ++ "/plain/r1/.git/swarm")
  put (t.d ++ "/plain/r1/.git/swarm/swarm.db") ""
  let o : Opts := { ok := false, cwd := some (t.d ++ "/plain"), env := [("SWARM_DB", none)] }
  let r ← t.sw "c" ["board"] o
  eq (decide (r.code ≠ 0)) true
  has r.stderr s!"r1: export SWARM_DB={t.d}/plain/r1/.git/swarm/swarm.db"
  let r ← t.sw "c" ["board"] { o with cwd := some (t.d ++ "/plain/r1/.git") }
  has r.stderr "cd into the swarm's repo"
  let r ← t.sw "c" ["machine"] o
  eq r.code 0
  has r.stdout "machine:"

def tests : List Case := [
  ("test_join_then_watchd_records_space", test_join_then_watchd_records_space),
  ("test_watchd_start_leaves_another_swarms_terminal", test_watchd_start_leaves_another_swarms_terminal),
  ("test_join_registers_without_watchd", test_join_registers_without_watchd),
  ("test_no_repo_label_finds_the_db", test_no_repo_label_finds_the_db),
  ("test_no_repo_names_the_swarms_below", test_no_repo_names_the_swarms_below),
  ("test_join_records_space_and_labels", test_join_records_space_and_labels),
  ("test_join_refused_outside_space_even_with_takeover", test_join_refused_outside_space_even_with_takeover),
  ("test_join_refused_for_another_swarms_communicator", test_join_refused_for_another_swarms_communicator),
  ("test_watchd_launches_missing_communicator_in_space", test_watchd_launches_missing_communicator_in_space),
  ("test_watchd_leaves_a_good_communicator", test_watchd_leaves_a_good_communicator),
  ("test_watchd_holds_autospawn_when_comms_cant_launch", test_watchd_holds_autospawn_when_comms_cant_launch)]

end SwarmLean.Tests.Cli.Comms

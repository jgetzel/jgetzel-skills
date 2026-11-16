import Tests.Cli.WatchdRun
import Claims.Ledger

/-! sw-compute.md §5: `swarm run` / `swarm compute` over the ledger (the script's own cases are claim/Tests/Script.lean's; the
fixture's machine is an idle 8-core, 16G one; the fake hc's `laptop` has its own home and so its own ledger). -/

namespace SwarmLean.Tests.Cli.Compute
open SwarmLean.Tests.Cli SwarmLean.Tests.Cli.WatchdRun
open Lean (Json toJson)

/-- The script's op against the ledger under `st`. -/
def scr (t : T) (st : String) (args : List String) : IO R :=
  t.exec (["sh", "-c", Claims.SCRIPT, "sh"] ++ args) { env := [("XDG_STATE_HOME", some st)] }

/-- `try` of `cores` and 1 MiB, no estimate, as holder `holder`, its one-line answer. -/
def try_ (t : T) (st id cores : String) (holder := "t") : IO String :=
  return strip (← scr t st ["try", id, cores, "1024", "-", holder, "w", "cmd"]).stdout

/-- Runs an App action. -/
def app (act : App α) : IO α := do
  match ← (act.run.run { conn := ← IO.mkRef none }) with
  | .ok a => pure a
  | .error e => fail s!"exit {e.code}"

/-- Records `run` rows of these walls for `cmd` in the history. -/
def recordRuns (cmd : String) (ws : List Int) (source := "run") : IO Unit := do
  for w in ws do
    discard <| app (SwarmLean.Cost.record { ts := 1, machine := "elsewhere", repo := "repo", agent := "a", source, cmd, wall_s := w, peak_kb := 0 } : App Bool)

/-- The history's rows (key, source, wall_s, machine) of a key. -/
def costRows (key : String) : IO (List (String × String × Int × String)) := do
  let h ← Sqlite.Conn.open (← app SwarmLean.Cost.path) true
  let rs ← h.query s!"select key,source,wall_s,machine from cmd where key='{key}' order by id"
  return rs.toList.map fun r => (SwarmLean.Cost.vs (r.getD 0 .null), SwarmLean.Cost.vs (r.getD 1 .null),
    SwarmLean.Cost.vi (r.getD 2 .null), SwarmLean.Cost.vs (r.getD 3 .null))

/-- The state dir `swarm run` and the script share in these tests. -/
def state (t : T) : String := t.d ++ "/.state"

/-- Fills the machine's cores with a claim that outlives the test. -/
def fill (t : T) (cores : String) : IO Unit := discard <| try_ t (state t) "hog" cores

/-- Waits (100 ms steps, up to 20 s) for `p` to hold. -/
def until_ (p : IO Bool) : IO Unit := do
  for _ in [0:200] do
    if ← p then return
    IO.sleep 100
  fail "timed out"

/-- `swarm run …` in the background as `who`: its pid, once it has one; its stdout, stderr and exit code are `o`, `e`, `rc`
under t.d. -/
def bg (t : T) (who : String) (args : List String) : IO Int := do
  let bp ← basePath
  let path := match ← t.fakebin with | some fb => s!"{fb}:{bp}" | none => bp
  let D := shquote t.d
  let env : List (String × Option String) := [("SWARM_DB", some t.db), ("SWARM_NAME", some who), ("PATH", some path),
    ("XDG_DATA_HOME", some (← xdg))]
  discard <| t.exec (["sh", "-c", s!"( \"$@\" >{D}/o 2>{D}/e & p=$!; echo $p > {D}/pid; wait $p; echo $? > {D}/rc ) >/dev/null 2>&1 &",
    "sh", (← swarmBin), "run"] ++ args) { env, cwd := some (← t.cwdOf who) }
  until_ (exists_ (t.d ++ "/pid"))
  return (strip (← readF [t.d, "pid"])).toInt!

def claimsHere (t : T) : IO Nat := do
  let r ← scr t (state t) ["ls"]
  return ((splitlines r.stdout).filter (·.startsWith "c ")).length

def test_run_env_and_claim_released (t : T) : IO Unit := do
  let cmd := "echo cores=$SWARM_CORES mem=$SWARM_MEM_KB mk=$MAKEFLAGS cargo=$CARGO_BUILD_JOBS nix=$NIX_BUILD_CORES; " ++
    "echo \"$NIX_CONFIG\" | tr '\\n' '|'; echo; echo claims=$(ls \"$XDG_STATE_HOME/swarm-compute/claims\" | wc -l)"
  let r ← t.sw "b" ["run", "--cores", "3", "--mem", "1.5", "--", cmd]
  has r.stdout "cores=3 mem=1572864 mk=-j3 cargo=3 nix=3"
  has r.stdout "cores = 3|max-jobs = 1|"
  has r.stdout "claims=1"
  has r.stderr "claiming 3 cores, 1.5G"
  eq (← claimsHere t) 0
  let st ← parse (((← t.q1 "select data from event where kind='job-start'").f "data").s?.getD "")
  eq (toJson [st.f "cores", st.f "mem_kb"]) (json% [3, 1572864])
  -- no flags, no history: the default
  has (← t.sw "b" ["run", "--", "echo $SWARM_CORES"]).stdout "2\n"

def test_run_sized_from_history (t : T) : IO Unit := do
  let rec_ : SwarmLean.Cost.Rec := { ts := 1, machine := "elsewhere", repo := "repo", agent := "a", cmd := "make all", wall_s := 100, cpu_s := 450, peak_kb := 4000000 }
  match ← ((SwarmLean.Cost.record rec_ : App Bool).run.run { conn := ← IO.mkRef none }) with
  | .ok _ => pure ()
  | .error _ => fail "cost.record exited"
  let r ← t.sw "b" ["run", "--", "make all 2>/dev/null; echo $SWARM_CORES $SWARM_MEM_KB"]
  has r.stdout "5 5000000"
  -- a `swarm run` row's cpu_s is a %CPU sample: it never raises the cores
  let big : SwarmLean.Cost.Rec := { ts := 2, machine := "elsewhere", repo := "repo", agent := "a", cmd := "make all", wall_s := 100, cpu_s := 5000, peak_kb := 1, source := "run" }
  match ← ((SwarmLean.Cost.record big : App Bool).run.run { conn := ← IO.mkRef none }) with
  | .ok _ => pure ()
  | .error _ => fail "cost.record exited"
  has (← t.sw "b" ["run", "--", "make all 2>/dev/null; echo $SWARM_CORES"]).stdout "5\n"
  has r.stderr "from the history"

def test_run_routes_to_the_second_machine_when_the_first_is_full (t : T) : IO Unit := do
  let home ← fakeRemote t
  mkdir (t.wt ++ "/.claude")
  put (t.wt ++ "/.claude/swarm.json") (json% {"run": {"machines": ["laptop"]}}).compress
  fill t "8"
  let r ← t.sw "b" ["run", "--", "cat $HOME/.local/state/swarm-compute/claims/* | cut -d' ' -f1,3 | tr -d 0-9 ; echo hi"]
  has r.stdout "hi"; has r.stdout "on laptop"
  has r.stdout " p\n"  -- the holder became the job's shell
  eq (← claimsHere t) 1  -- the filler only
  eq (splitlines (← t.exec ["ls", home ++ "/.local/state/swarm-compute/claims"]).stdout).length 0

def test_run_a_machine_gone_is_retried (t : T) : IO Unit := do
  discard <| fakeRemote t
  mkdir (t.wt ++ "/.claude")
  put (t.wt ++ "/.claude/swarm.json") (json% {"run": {"machines": ["laptop"]}}).compress
  put (t.d ++ "/exec.fail") ""
  -- the first round: here is off and laptop does not answer, no wait: 255
  discard <| t.sw "b" ["compute", "off", "here"]
  eq (← t.sw "b" ["run", "--", "true"] { ok := false }).code 255
  discard <| t.sw "b" ["compute", "on", "here"]
  -- a later round: here never fits, laptop is gone: it keeps waiting, and runs on laptop when that answers
  fill t "8"
  discard <| bg t "b" ["--", "echo ran"]
  until_ (return (← slurp (t.d ++ "/e")).any (subIn · "waiting for room"))
  discard <| t.sw "b" ["compute", "cap", "here", "--cores", "1"]
  IO.sleep 1000
  eq (← slurp (t.d ++ "/rc")) (none : Option String)
  IO.FS.removeFile (t.d ++ "/exec.fail")
  until_ (do return (subIn ((← slurp (t.d ++ "/o")).getD "") "on laptop"))

def test_run_waits_and_runs_when_a_claim_is_dropped (t : T) : IO Unit := do
  fill t "8"
  discard <| bg t "b" ["--", "echo ran"]
  until_ (return (← slurp (t.d ++ "/e")).any (subIn · "waiting for room"))
  IO.sleep 1300
  eq (← slurp (t.d ++ "/rc")) (none : Option String)
  discard <| scr t (state t) ["drop", "hog"]
  until_ (exists_ (t.d ++ "/rc"))
  let out := (← slurp (t.d ++ "/o")).getD ""
  has out "ran"; has out ", waited 0m0"
  let en ← parse (((← t.q1 "select data from event where kind='job-end'").f "data").s?.getD "")
  eq (decide ((en.f "wait_s").i ≥ 1)) true
  eq (← claimsHere t) 0

def test_run_nothing_can_fit_is_255 (t : T) : IO Unit := do
  let r ← t.sw "b" ["run", "--cores", "9", "--", "true"] { ok := false }
  eq r.code 255
  has r.stderr "nothing can run this job"; has r.stderr "needs more than the cap (8 cores"
  discard <| t.sw "b" ["compute", "cap", "here", "--cores", "2"]
  has (← t.sw "b" ["compute"]).stdout "here: 0 of 2 cores claimed (cap 2 of 8, 0.0 busy)"
  eq (← t.sw "b" ["run", "--cores", "3", "--", "true"] { ok := false }).code 255
  discard <| t.sw "b" ["compute", "off", "here"]
  has (← t.sw "b" ["compute"]).stdout "here: off"
  let r ← t.sw "b" ["run", "--", "true"] { ok := false }
  eq r.code 255; has r.stderr "here: off"
  discard <| t.sw "b" ["compute", "on", "here"]
  discard <| t.sw "b" ["compute", "cap", "here", "--cores", "all"]
  eq (← t.sw "b" ["run", "--", "true"]).code 0
  -- the machines come from hc machine ls
  discard <| fakeRemote t
  has (← t.sw "b" ["compute"]).stdout "laptop: 0 of 8 cores claimed"
  eq ((← parse (← t.sw "b" ["compute", "--json"]).stdout).f "laptop" |>.f "ncpu") (8 : Int)

def test_run_claim_is_gone_after_a_killed_job (t : T) : IO Unit := do
  let p ← bg t "b" ["--cores", "2", "--", s!"echo $$ > {t.d}/job; exec sleep 60"]
  until_ (exists_ (t.d ++ "/job"))
  eq (← claimsHere t) 1
  has (← t.sw "b" ["compute"]).stdout "2 cores"
  let j := strip (← readF [t.d, "job"])
  discard <| t.exec ["kill", "-9", toString p]
  discard <| t.exec ["kill", "-9", j]
  eq (← claimsHere t) 0

def test_run_estimate_into_the_claim (t : T) : IO Unit := do
  -- 12 `run` rows of 1..12 s: the 90th percentile is 11; a `swarm` row of 1000 s in the window does not count
  let cmd := "cat $XDG_STATE_HOME/swarm-compute/claims/*"
  recordRuns cmd ((List.range' 1 12).map Int.ofNat)
  recordRuns cmd [1000] "swarm"
  let r ← t.sw "b" ["run", "--", cmd]
  has r.stdout " ~11 "
  has r.stderr ", ~11s ("
  -- no history, no estimate
  let r ← t.sw "b" ["run", "--", "cut -d' ' -f5 $XDG_STATE_HOME/swarm-compute/claims/*"]
  eq (strip r.stdout |> splitlines |>.head!) "b"
  hasnt r.stderr ", ~"

def test_run_all_is_the_whole_machine (t : T) : IO Unit := do
  let r ← t.sw "b" ["run", "--cores", "all", "--", "echo $SWARM_CORES $SWARM_MEM_KB"]
  has r.stdout "8 16777216"
  has r.stderr "claiming the whole machine"
  eq (← t.sw "b" ["run", "--cores", "all", "--mem", "1", "--", "true"] { ok := false }).code 1
  -- under a cap below the machine it is refused, and the message says so
  discard <| t.sw "b" ["compute", "cap", "here", "--cores", "4"]
  let r ← t.sw "b" ["run", "--cores", "all", "--", "true"] { ok := false }
  eq r.code 255; has r.stderr "needs the whole machine, and the cap is lower (4 cores"

def test_run_lowest_priority (t : T) : IO Unit := do
  has (← t.sw "b" ["run", "--", "echo nice=$(nice)"]).stdout "nice=19"
  if (← t.exec ["ionice", "-c3", "true"]).code == 0 then
    has (← t.sw "b" ["run", "--", "ionice -p $$"]).stdout "idle"
  discard <| fakeRemote t
  has (← t.sw "b" ["run", "--on", "laptop", "--", "echo nice=$(nice)"]).stdout "nice=19"

def test_run_records_every_job (t : T) : IO Unit := do
  discard <| t.sw "b" ["run", "--", "true"]
  let rows ← costRows "true"
  eq rows.length 1
  let (k, src, w, _) := rows.head!
  eq k "true"; eq src "run"; eq (decide (w < 60)) true
  -- a remote job with a prefix is filed under the user's command
  discard <| fakeRemote t
  mkdir (t.wt ++ "/.claude")
  put (t.wt ++ "/.claude/swarm.json") (json% {"run": {"prefix": "env X=1"}}).compress
  discard <| t.sw "b" ["run", "--on", "laptop", "--", "echo hi"]
  let rows ← costRows "echo hi"
  eq rows.length 1
  eq (rows.head!.2.1) "run"

def test_compute_reserve_and_the_one_machine_view (t : T) : IO Unit := do
  discard <| t.sw "b" ["compute", "reserve", "here", "3"]
  let j ← parse (← t.sw "b" ["compute", "--json", "here"]).stdout
  eq ((j.f "here").f "reserve_cores") (3 : Int); eq ((j.f "here").f "limit_cores") (5 : Int)
  has (← t.sw "b" ["compute", "here"]).stdout "0 of 5 cores claimed (cap 8 of 8, 3 reserved, 0.0 busy)"
  has (← t.sw "b" ["compute"]).stdout "3 reserved"
  discard <| t.sw "b" ["compute", "reserve", "here", "0"]
  hasnt (← t.sw "b" ["compute", "here"]).stdout "reserved"
  eq (← t.sw "b" ["compute", "reserve", "here", "x"] { ok := false }).code 1

def tests : List Case := [
  ("test_run_env_and_claim_released", test_run_env_and_claim_released),
  ("test_run_sized_from_history", test_run_sized_from_history),
  ("test_run_routes_to_the_second_machine_when_the_first_is_full", test_run_routes_to_the_second_machine_when_the_first_is_full),
  ("test_run_a_machine_gone_is_retried", test_run_a_machine_gone_is_retried),
  ("test_run_waits_and_runs_when_a_claim_is_dropped", test_run_waits_and_runs_when_a_claim_is_dropped),
  ("test_run_nothing_can_fit_is_255", test_run_nothing_can_fit_is_255),
  ("test_run_claim_is_gone_after_a_killed_job", test_run_claim_is_gone_after_a_killed_job),
  ("test_run_estimate_into_the_claim", test_run_estimate_into_the_claim),
  ("test_run_all_is_the_whole_machine", test_run_all_is_the_whole_machine),
  ("test_run_lowest_priority", test_run_lowest_priority),
  ("test_run_records_every_job", test_run_records_every_job),
  ("test_compute_reserve_and_the_one_machine_view", test_compute_reserve_and_the_one_machine_view)]

end SwarmLean.Tests.Cli.Compute

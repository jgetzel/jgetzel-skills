import Tests.Cli.WatchdRun
import SwarmLean.Lib.Compute

/-! sw-compute.md §5: the ledger's script against a scratch XDG_STATE_HOME, and `swarm run` / `swarm compute` over it (the
fixture's machine is an idle 8-core, 16G one; the fake hc's `laptop` has its own home and so its own ledger). -/

namespace SwarmLean.Tests.Cli.Compute
open SwarmLean.Tests.Cli SwarmLean.Tests.Cli.WatchdRun
open Lean (Json toJson)

/-- The script's op against the ledger under `st`. -/
def scr (t : T) (st : String) (args : List String) : IO R :=
  t.exec (["sh", "-c", Compute.SCRIPT, "sh"] ++ args) { env := [("XDG_STATE_HOME", some st)] }

/-- `try` of `cores` and 1 MiB as holder `holder`, its one-line answer. -/
def try_ (t : T) (st id cores : String) (holder := "t") : IO String :=
  return strip (← scr t st ["try", id, cores, "1024", holder, "w", "cmd"]).stdout

def test_script_50_parallel_grant_exactly_4 (t : T) : IO Unit := do
  let st := t.d ++ "/s1"
  discard <| scr t st ["cap", "8", "-"]
  -- one sh starts the 50: as many Lean tasks each spawning, a CI runner's worker could fork no more (ENOMEM)
  let out := t.d ++ "/s1-answers"
  mkdir out
  discard <| t.exec ["sh", "-c", "k=0; while [ $k -lt 50 ]; do sh -c \"$1\" sh try c$k 2 1024 t w cmd >\"$2/$k\" & k=$((k + 1)); done; wait",
    "sh", Compute.SCRIPT, out] { env := [("XDG_STATE_HOME", some st)] }
  let rs ← (List.range 50).mapM fun k => return strip ((← slurp s!"{out}/{k}").getD "")
  eq (rs.filter (·.startsWith "ok")).length 4 s!"grants; answers {rs.eraseDups}"
  eq ((splitlines (← scr t st ["ls"]).stdout).filter (·.startsWith "c ")).length 4

def test_script_dead_claims_are_not_counted (t : T) : IO Unit := do
  let st := t.d ++ "/s2"
  let dead := strip (← t.exec ["sh", "-c", "echo $$"]).stdout
  mkdir (st ++ "/swarm-compute/claims")
  put (st ++ "/swarm-compute/claims/a") s!"8 1024 p{dead} 1 w x\n"
  put (st ++ "/swarm-compute/claims/b") "8 1024 t1 1 w x\n"
  eq (← try_ t st "n" "8") "ok 8"
  eq (← exists_ (st ++ "/swarm-compute/claims/a")) false
  eq (← exists_ (st ++ "/swarm-compute/claims/b")) false

def test_script_an_old_lock_without_a_live_holder_is_broken (t : T) : IO Unit := do
  let st := t.d ++ "/s5"
  let dead := strip (← t.exec ["sh", "-c", "echo $$"]).stdout
  mkdir (st ++ "/swarm-compute/lock")
  put (st ++ "/swarm-compute/lock/pid") s!"{dead}\n"
  discard <| t.exec ["touch", "-t", "202001010000", st ++ "/swarm-compute/lock"]
  eq (← try_ t st "a" "1") "ok 1"
  -- one whose holder died before writing its pid
  mkdir (st ++ "/swarm-compute/lock")
  discard <| t.exec ["touch", "-t", "202001010000", st ++ "/swarm-compute/lock"]
  eq (← try_ t st "b" "1") "ok 1"

def test_script_older_ticket_holds_back_younger (t : T) : IO Unit := do
  let st := t.d ++ "/s3"
  mkdir (st ++ "/swarm-compute/queue")
  put (st ++ "/swarm-compute/queue/old") s!"{(← now t) - 5} 8 1024 w\n"
  has (← try_ t st "young" "1") "wait 8 16777216 1"
  eq (← try_ t st "old" "8") "ok 8"
  -- the old one is served; the young one's ticket stays until it is granted or dropped
  eq (← try_ t st "young" "1") "wait 0 16776192 0"
  discard <| scr t st ["drop", "old"]
  eq (← try_ t st "young" "1") "ok 1"
  eq (← exists_ (st ++ "/swarm-compute/queue/young")) false

def test_script_never_off_and_all (t : T) : IO Unit := do
  let st := t.d ++ "/s4"
  discard <| scr t st ["cap", "4", "-"]
  eq (← try_ t st "big" "5") "never 4 16777216"
  discard <| scr t st ["off"]
  eq (← try_ t st "x" "1") "off"
  discard <| scr t st ["on"]
  eq (← try_ t st "one" "2") "ok 2"
  has (← try_ t st "every" "all") "wait"
  discard <| scr t st ["drop", "one"]
  eq (← try_ t st "every" "all") "ok 4"
  -- `=` keeps a field of the cap
  discard <| scr t st ["cap", "=", "2048"]
  eq (strip (← scr t st ["ls"]).stdout |> splitlines |>.head!) "8 0.00 16777216 16777216 4 2048 0"

def test_script_compute_dir_overrides_the_ledger (t : T) : IO Unit := do
  let st := t.d ++ "/s5"
  discard <| t.exec ["sh", "-c", Compute.SCRIPT, "sh", "cap", "3", "-"] { env := [("XDG_STATE_HOME", some st), ("SWARM_COMPUTE_DIR", some (st ++ "/other"))] }
  eq (strip (← readF [st, "other", "cap"])) "3 -"
  eq (← exists_ (st ++ "/swarm-compute/cap")) false

def test_script_arithmetic_of_the_awk_programs (t : T) : IO Unit := do
  let busy ← t.exec ["awk", "-v", "n=4", Compute.BUSY_AWK] { input := some "cpu 100 0 100 800 0 0 0 0 0 0\ncpu 300 0 200 1000 0 0 0 0 0 0\n" }
  eq busy.stdout "2.40"
  let vm := "Mach Virtual Memory Statistics: (page size of 16384 bytes)\nPages free:                               12345.\nPages active:                            200000.\nPages inactive:                          100000.\nPages speculative:                         5000.\nPages throttled:                              0.\nPages wired down:                         80000.\nPages purgeable:                           2655.\n"
  eq (strip (← t.exec ["awk", Compute.DARWIN_MEM_AWK] { input := some vm }).stdout) (toString (120000 * 16))

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

def tests : List Case := [
  ("test_script_50_parallel_grant_exactly_4", test_script_50_parallel_grant_exactly_4),
  ("test_script_an_old_lock_without_a_live_holder_is_broken", test_script_an_old_lock_without_a_live_holder_is_broken),
  ("test_script_dead_claims_are_not_counted", test_script_dead_claims_are_not_counted),
  ("test_script_older_ticket_holds_back_younger", test_script_older_ticket_holds_back_younger),
  ("test_script_never_off_and_all", test_script_never_off_and_all),
  ("test_script_compute_dir_overrides_the_ledger", test_script_compute_dir_overrides_the_ledger),
  ("test_script_arithmetic_of_the_awk_programs", test_script_arithmetic_of_the_awk_programs),
  ("test_run_env_and_claim_released", test_run_env_and_claim_released),
  ("test_run_sized_from_history", test_run_sized_from_history),
  ("test_run_routes_to_the_second_machine_when_the_first_is_full", test_run_routes_to_the_second_machine_when_the_first_is_full),
  ("test_run_a_machine_gone_is_retried", test_run_a_machine_gone_is_retried),
  ("test_run_waits_and_runs_when_a_claim_is_dropped", test_run_waits_and_runs_when_a_claim_is_dropped),
  ("test_run_nothing_can_fit_is_255", test_run_nothing_can_fit_is_255),
  ("test_run_claim_is_gone_after_a_killed_job", test_run_claim_is_gone_after_a_killed_job)]

end SwarmLean.Tests.Cli.Compute

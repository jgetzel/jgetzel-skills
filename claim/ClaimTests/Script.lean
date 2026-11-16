import ClaimTests.Harness

/-! The ledger script against a scratch XDG_STATE_HOME (moved from swarm's Tests/Cli/Compute.lean; the fixture's machine is an
idle 8-core, 16G one). -/

namespace Claims.Tests.Script
open Claims Claims.Tests

def now (t : T) : IO Int := return (strip (← t.exec ["date", "+%s"]).stdout).toInt!

/-- `try` of `cores` and 1 MiB as holder `holder`, its one-line answer. -/
def try_ (t : T) (st id cores : String) (holder := "t") : IO String :=
  return strip (← t.scr st ["try", id, cores, "1024", holder, "w", "cmd"]).stdout

def test_script_50_parallel_grant_exactly_4 (t : T) : IO Unit := do
  let st := t.d ++ "/s1"
  discard <| t.scr st ["cap", "8", "-"]
  -- one sh starts the 50: as many Lean tasks each spawning, a CI runner's worker could fork no more (ENOMEM)
  let out := t.d ++ "/s1-answers"
  mkdir out
  discard <| t.exec ["sh", "-c", "k=0; while [ $k -lt 50 ]; do sh -c \"$1\" sh try c$k 2 1024 t w cmd >\"$2/$k\" & k=$((k + 1)); done; wait",
    "sh", SCRIPT, out] [("XDG_STATE_HOME", some st)]
  let rs ← (List.range 50).mapM fun k => return strip ((← slurp s!"{out}/{k}").getD "")
  eq (rs.filter (·.startsWith "ok")).length 4 s!"grants; answers {rs.eraseDups}"
  eq ((splitlines (← t.scr st ["ls"]).stdout).filter (·.startsWith "c ")).length 4

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
  discard <| t.scr st ["drop", "old"]
  eq (← try_ t st "young" "1") "ok 1"
  eq (← exists_ (st ++ "/swarm-compute/queue/young")) false

def test_script_never_off_and_all (t : T) : IO Unit := do
  let st := t.d ++ "/s4"
  discard <| t.scr st ["cap", "4", "-"]
  eq (← try_ t st "big" "5") "never 4 16777216"
  discard <| t.scr st ["off"]
  eq (← try_ t st "x" "1") "off"
  discard <| t.scr st ["on"]
  eq (← try_ t st "one" "2") "ok 2"
  has (← try_ t st "every" "all") "wait"
  discard <| t.scr st ["drop", "one"]
  eq (← try_ t st "every" "all") "ok 4"
  -- `=` keeps a field of the cap
  discard <| t.scr st ["cap", "=", "2048"]
  eq (strip (← t.scr st ["ls"]).stdout |> splitlines |>.head!) "8 0.00 16777216 16777216 4 2048 0"

def test_script_compute_dir_overrides_the_ledger (t : T) : IO Unit := do
  let st := t.d ++ "/s5"
  discard <| t.exec ["sh", "-c", SCRIPT, "sh", "cap", "3", "-"] [("XDG_STATE_HOME", some st), ("SWARM_COMPUTE_DIR", some (st ++ "/other"))]
  eq (strip (← readF [st, "other", "cap"])) "3 -"
  eq (← exists_ (st ++ "/swarm-compute/cap")) false

def test_script_arithmetic_of_the_awk_programs (t : T) : IO Unit := do
  let busy ← t.exec ["awk", "-v", "n=4", BUSY_AWK] (input := some "cpu 100 0 100 800 0 0 0 0 0 0\ncpu 300 0 200 1000 0 0 0 0 0 0\n")
  eq busy.stdout "2.40"
  let vm := "Mach Virtual Memory Statistics: (page size of 16384 bytes)\nPages free:                               12345.\nPages active:                            200000.\nPages inactive:                          100000.\nPages speculative:                         5000.\nPages throttled:                              0.\nPages wired down:                         80000.\nPages purgeable:                           2655.\n"
  eq (strip (← t.exec ["awk", DARWIN_MEM_AWK] (input := some vm)).stdout) (toString (120000 * 16))

def tests : List Case := [
  ("test_script_50_parallel_grant_exactly_4", test_script_50_parallel_grant_exactly_4),
  ("test_script_dead_claims_are_not_counted", test_script_dead_claims_are_not_counted),
  ("test_script_an_old_lock_without_a_live_holder_is_broken", test_script_an_old_lock_without_a_live_holder_is_broken),
  ("test_script_older_ticket_holds_back_younger", test_script_older_ticket_holds_back_younger),
  ("test_script_never_off_and_all", test_script_never_off_and_all),
  ("test_script_compute_dir_overrides_the_ledger", test_script_compute_dir_overrides_the_ledger),
  ("test_script_arithmetic_of_the_awk_programs", test_script_arithmetic_of_the_awk_programs)]

end Claims.Tests.Script

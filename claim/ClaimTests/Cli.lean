import ClaimTests.Harness

/-! `claim` the executable, run from a directory that is no git repo, against the fixture's idle 8-core machine. -/

namespace Claims.Tests.Cli
open Claims Claims.Tests

/-- The `claim` next to claim-tests, else $CLAIM_BIN. -/
def bin : IO String := do
  if let some b ← IO.getEnv "CLAIM_BIN" then if b ≠ "" then return b
  return ((← IO.appPath).parent.getD ".").toString ++ "/claim"

/-- `claim args…` in the test dir. -/
def claim (t : T) (args : List String) : IO R := do t.exec ((← bin) :: args) (cwd := some t.d)

def test_claim_help (t : T) : IO Unit := do
  has (← claim t ["-h"]).stdout "claim: sized claims"

def test_claim_show_and_op_outside_a_repo (t : T) : IO Unit := do
  has (← claim t []).stdout "here: 0 of 8 cores claimed (cap 8 of 8, 0.0 busy), 0.0 of 16.0G claimed (16.0G available)"
  eq (splitlines (← claim t ["op", "here", "ls"]).stdout).head! "8 0.00 16777216 16777216 8 16777216 0 0 0"
  eq (words (splitlines (← claim t ["op", "here", "ls"]).stdout).head!).length 9
  has (← claim t ["--json"]).stdout "\"ncpu\":8"
  eq (← claim t ["op", "here", "bogus"]).code 2

def test_claim_cap_off_on (t : T) : IO Unit := do
  discard <| claim t ["cap", "here", "--cores", "3"]
  has (← claim t []).stdout "cap 3 of 8"
  discard <| claim t ["off", "here"]
  eq (strip (← claim t []).stdout) "here: off" "off, nothing claimed"
  discard <| claim t ["on", "here"]
  discard <| claim t ["cap", "here", "--cores", "all"]
  has (← claim t []).stdout "cap 8 of 8"
  eq (← claim t ["cap", "nowhere", "--cores", "2"]).code 1

def test_claim_run_holds_the_claim_while_it_runs (t : T) : IO Unit := do
  let b ← bin
  let r ← claim t ["run", "--cores", "3", "--mem", "1.5", "--", "sh", "-c", s!"echo $SWARM_CORES $SWARM_MEM_KB $MAKEFLAGS; {shquote b} op here ls"]
  eq r.code 0
  has r.stdout "3 1572864 -j3"
  has r.stdout "c 3 1572864 p"
  -- and drops it
  eq ((splitlines (← claim t ["op", "here", "ls"]).stdout).filter (·.startsWith "c ")).length 0

def test_claim_run_exits_with_the_commands_code (t : T) : IO Unit := do
  eq (← claim t ["run", "--cores", "1", "--", "sh", "-c", "exit 7"]).code 7
  eq (← claim t ["run", "--cores", "1", "--", "true"]).code 0

def test_claim_run_nothing_fits_is_255 (t : T) : IO Unit := do
  let r ← claim t ["run", "--cores", "9", "--", "true"]
  eq r.code 255
  has r.stderr "nothing can run this job"; has r.stderr "needs more than the cap (8 cores"

def test_claim_run_at_the_lowest_priority_and_with_its_claim (t : T) : IO Unit := do
  let r ← claim t ["run", "--cores", "2", "--", "sh", "-c", "echo $SWARM_CORES nice=$(nice)"]
  eq r.stdout "2 nice=19\n"; eq r.code 0
  eq ((splitlines (← claim t ["op", "here", "ls"]).stdout).filter (·.startsWith "c ")).length 0
  -- where ionice works the job's I/O class is idle
  if (← t.exec ["ionice", "-c3", "true"]).code == 0 then
    has (← claim t ["run", "--", "sh", "-c", "ionice -p $$"]).stdout "idle"

def test_claim_run_est_is_in_the_claim_line (t : T) : IO Unit := do
  let b ← bin
  has (← claim t ["run", "--est", "90", "--", "sh", "-c", s!"{shquote b} op here ls"]).stdout " ~90 "
  eq (← claim t ["run", "--est", "x", "--", "true"]).code 1

/-- `claim run …` in the background: its stdout, stderr and exit code are `o`, `e`, `rc` under the test dir. -/
def bgRun (t : T) (args : List String) : IO Unit := do
  let D := shquote t.d
  discard <| t.exec (["sh", "-c", s!"( \"$@\" >{D}/o 2>{D}/e; echo $? > {D}/rc ) >/dev/null 2>&1 </dev/null &", "sh", ← bin, "run"] ++ args) (cwd := some t.d)

/-- Waits (100 ms steps, up to 20 s) for `p`. -/
def until_ (p : IO Bool) : IO Unit := do
  for _ in [0:200] do
    if ← p then return
    IO.sleep 100
  fail "timed out"

def test_claim_run_waits_while_the_ledger_is_full (t : T) : IO Unit := do
  let st := t.d ++ "/.state"
  has (← t.scr st ["try", "hog", "8", "1024", "-", "t", "w", "cmd"]).stdout "ok 8"
  bgRun t ["--cores", "2", "--", "echo", "ran"]
  until_ (return (← slurp (t.d ++ "/e")).any (subIn · "waiting for room"))
  IO.sleep 600
  eq (← exists_ (t.d ++ "/rc")) false
  discard <| t.scr st ["drop", "hog"]
  until_ (exists_ (t.d ++ "/rc"))
  eq (strip (← readF [t.d, "o"])) "ran"; eq (strip (← readF [t.d, "rc"])) "0"

/-- A hc that knows one machine and answers nothing else. -/
def hcWith (t : T) : IO Unit := do
  put (t.d ++ "/bin/hc") "#!/bin/sh\ncase \"$1 $2\" in \"machine ls\") echo '{\"machines\": [{\"name\": \"laptop\", \"state\": \"connected\"}]}';; *) exit 1;; esac\n"

def test_claim_reserve_and_the_one_machine_view (t : T) : IO Unit := do
  hcWith t
  eq (← claim t ["reserve", "here", "3", "--mem", "2"]).code 0
  let j ← claim t ["--json", "here"]
  has j.stdout "\"reserve_cores\":3"; has j.stdout "\"reserve_mem_kb\":2097152"; has j.stdout "\"limit_cores\":5"
  has j.stdout "{\"here\":"; hasnt j.stdout "laptop"
  has (← claim t ["--json"]).stdout "laptop"
  let x ← claim t ["here"]
  has x.stdout "3 reserved, "; has x.stdout "2.0G reserved, "; has x.stdout "0 of 5 cores claimed"
  -- the reservation is the whole of it: no --mem is no memory
  eq (← claim t ["reserve", "here", "1"]).code 0
  has (← claim t ["--json", "here"]).stdout "\"reserve_mem_kb\":0"
  eq (← claim t ["reserve", "here", "0"]).code 0
  let j ← claim t ["--json", "here"]
  has j.stdout "\"reserve_cores\":0"; has j.stdout "\"limit_cores\":8"
  hasnt (← claim t ["here"]).stdout "reserved"
  eq (← claim t ["reserve", "here", "-1"]).code 1
  eq (← claim t ["reserve", "here", "x"]).code 1
  eq (← claim t ["reserve", "here", "2", "--mem", "x"]).code 1
  eq (← claim t ["reserve", "nowhere", "2"]).code 1
  eq (← claim t ["nowhere"]).code 1

def test_claim_run_all_is_exclusive_and_refuses_mem (t : T) : IO Unit := do
  eq (← claim t ["run", "--cores", "all", "--mem", "1", "--", "true"]).code 1
  let r ← claim t ["run", "--cores", "all", "--", "sh", "-c", "echo $SWARM_CORES $SWARM_MEM_KB"]
  eq r.stdout "8 16777216\n"
  -- held by a reservation: it waits, and runs when that is lifted
  discard <| claim t ["reserve", "here", "1"]
  bgRun t ["--cores", "all", "--", "echo", "alone"]
  until_ (return (← slurp (t.d ++ "/e")).any (subIn · "waiting for room"))
  discard <| claim t ["reserve", "here", "0"]
  until_ (exists_ (t.d ++ "/rc"))
  eq (strip (← readF [t.d, "o"])) "alone"

def test_claim_queue_shows_beside_the_claims (t : T) : IO Unit := do
  hcWith t
  eq (← claim t ["queue", "add", "here", "--id", "tq-1", "--who", "hpl-1", "--est", "1200", "--ttl", "600", "--owner", "timing-queue", "--", "timing", "run"]).code 0
  let x ← claim t ["here"]
  -- `since <n>s`: the clock may pass a second between the add and the show
  let pre := "  queued: hpl-1 timing run (owner timing-queue) ~20m, since "
  let some l := (splitlines x.stdout).find? (·.startsWith pre) | fail s!"missing {pre.quote}\n  in {x.stdout.quote}"
  let since := (l.drop pre.length).toString.toList
  unless since.length ≥ 2 && since.getLast? == some 's' && since.dropLast.all Char.isDigit do fail s!"since: {l.quote}"
  let j ← claim t ["--json", "here"]
  has j.stdout "\"queued\":[{"; has j.stdout "\"owner\":\"timing-queue\""; has j.stdout "\"est_s\":1200"
  -- the claim ledger is untouched
  has x.stdout "0 of 8 cores claimed"
  eq (← claim t ["queue", "add", "here", "--id", "tq-2", "--who", "w", "--pid", toString (← IO.Process.getPID), "--", "c"]).code 0
  eq (← claim t ["queue", "rm", "here", "tq-1"]).code 0
  hasnt (← claim t ["here"]).stdout "timing run"; has (← claim t ["here"]).stdout "queued: w c "
  eq (← claim t ["queue", "rm", "here", "tq-2"]).code 0
  has (← claim t ["--json", "here"]).stdout "\"queued\":[]"
  -- arguments
  eq (← claim t ["queue", "add", "here", "--who", "w", "--", "c"]).code 1
  eq (← claim t ["queue", "add", "here", "--id", "a", "--", "c"]).code 1
  eq (← claim t ["queue", "add", "here", "--id", "a", "--who", "w"]).code 1
  eq (← claim t ["queue", "add", "here", "--id", "a", "--who", "w", "--ttl", "0", "--", "c"]).code 1
  eq (← claim t ["queue", "add", "laptop", "--id", "a", "--who", "w", "--pid", "1", "--", "c"]).code 1
  eq (← claim t ["queue", "add", "nowhere", "--id", "a", "--who", "w", "--", "c"]).code 1

def tests : List Case := [
  ("test_claim_queue_shows_beside_the_claims", test_claim_queue_shows_beside_the_claims),
  ("test_claim_help", test_claim_help),
  ("test_claim_show_and_op_outside_a_repo", test_claim_show_and_op_outside_a_repo),
  ("test_claim_cap_off_on", test_claim_cap_off_on),
  ("test_claim_run_holds_the_claim_while_it_runs", test_claim_run_holds_the_claim_while_it_runs),
  ("test_claim_run_exits_with_the_commands_code", test_claim_run_exits_with_the_commands_code),
  ("test_claim_run_nothing_fits_is_255", test_claim_run_nothing_fits_is_255),
  ("test_claim_run_at_the_lowest_priority_and_with_its_claim", test_claim_run_at_the_lowest_priority_and_with_its_claim),
  ("test_claim_run_est_is_in_the_claim_line", test_claim_run_est_is_in_the_claim_line),
  ("test_claim_run_waits_while_the_ledger_is_full", test_claim_run_waits_while_the_ledger_is_full),
  ("test_claim_reserve_and_the_one_machine_view", test_claim_reserve_and_the_one_machine_view),
  ("test_claim_run_all_is_exclusive_and_refuses_mem", test_claim_run_all_is_exclusive_and_refuses_mem)]

end Claims.Tests.Cli

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
def bgRun (t : T) (args : List String) (env : List (String × Option String) := []) : IO Unit := do
  let D := shquote t.d
  discard <| t.exec (["sh", "-c", s!"( \"$@\" >{D}/o 2>{D}/e; echo $? > {D}/rc ) >/dev/null 2>&1 </dev/null &", "sh", ← bin, "run"] ++ args) env (cwd := some t.d)

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

/-- The wait line says what the head waits on: a claim without an estimate, by name, and unclaimed use with the yield's
time left. -/
def test_claim_run_wait_line_names_what_the_head_waits_on (t : T) : IO Unit := do
  let st := t.d ++ "/.state"
  has (← t.scr st ["try", "ci", "4", "1024", "-", "t", "hpl-ci", "bisect"]).stdout "ok 4"
  bgRun t ["--cores", "all", "--", "echo", "alone"]
  until_ (return (← slurp (t.d ++ "/e")).any (subIn · "waiting for room: here: whole machine waits on hpl-ci (4 cores, no estimate, "))
  discard <| t.scr st ["drop", "ci"]
  until_ (exists_ (t.d ++ "/rc"))
  eq (strip (← readF [t.d, "o"])) "alone"
  -- 4 busy cores no claim explains
  let busy := [("SWARM_COMPUTE_BUSY", some "4.00")]
  discard <| t.exec ["rm", "-f", t.d ++ "/rc", t.d ++ "/e"]
  bgRun t ["--cores", "all", "--", "echo", "alone"] busy
  until_ (return (← slurp (t.d ++ "/e")).any (subIn · "waiting for room: here: whole machine waits on 4.0 cores unclaimed use, yields in 10m"))
  discard <| t.scr st ["off"]
  until_ (exists_ (t.d ++ "/rc"))
  eq (strip (← readF [t.d, "rc"])) "255"

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

/-- The fixture's available memory, in KiB (Linux: the ledger reads macOS's own `vm_stat`, so these run on Linux alone). -/
def availKb (t : T) (kb : Nat) : IO Bool := do
  put (t.d ++ "/meminfo") s!"MemTotal:       16777216 kB\nMemAvailable:   {kb} kB\n"
  return strip (← t.exec ["uname"]).stdout != "Darwin"

/-- Board #104: a request short of memory by unclaimed use does not wait for it. A given --mem is refused with the reason;
a defaulted one is lowered to what is free, or refused under 1 GiB; the wait line says which and when. -/
def test_claim_run_short_of_memory_by_unclaimed_use (t : T) : IO Unit := do
  unless (← availKb t 4718592) do return
  let steady0 := [("SWARM_COMPUTE_STEADY_S", some "0")]
  let r ← t.exec [← bin, "run", "--cores", "1", "--mem", "10", "--", "echo", "ran"] steady0 (cwd := some t.d)
  eq r.code 255; hasnt r.stdout "ran"
  has r.stderr "nothing can run this job: it needs 10.0G, and unclaimed use leaves at most 4.5G with every claim ended"
  has r.stderr "Lower --mem."
  eq ((splitlines (← claim t ["op", "here", "ls"]).stdout).filter (·.startsWith "q ")).length 0
  -- the default 2G, with 1.5G free: lowered to nine tenths of it
  discard <| availKb t 1572864
  let r ← t.exec [← bin, "run", "--cores", "1", "--", "sh", "-c", "echo $SWARM_MEM_KB"] steady0 (cwd := some t.d)
  eq r.code 0; eq r.stdout "1415577\n"
  has r.stderr "not 2.0G: unclaimed use leaves at most 1.5G with every claim ended"
  -- with 0.5G free there is nothing to lower it to
  discard <| availKb t 524288
  let r ← t.exec [← bin, "run", "--cores", "1", "--", "echo", "ran"] steady0 (cwd := some t.d)
  eq r.code 255; has r.stderr "under the 1.0G it could be lowered to"
  -- before the steady time: the wait line says what will happen and when
  discard <| availKb t 1572864
  bgRun t ["--cores", "1", "--", "echo", "ran"]
  until_ (return (← slurp (t.d ++ "/e")).any (subIn · "held by unclaimed memory use; younger jobs go first; unclaimed use leaves at most 1.5G with every claim ended: lowered to "))
  discard <| claim t ["off", "here"]
  until_ (exists_ (t.d ++ "/rc"))
  eq (strip (← readF [t.d, "rc"])) "255"

/-- Board #104: a defaulted core count over the cap is lowered to it, with a line; a given one is refused. -/
def test_claim_run_defaulted_cores_over_the_cap_are_lowered (t : T) : IO Unit := do
  discard <| claim t ["cap", "here", "--cores", "1"]
  let r ← claim t ["run", "--", "sh", "-c", "echo $SWARM_CORES"]
  eq r.code 0; eq r.stdout "1\n"
  has r.stderr "claiming 1 cores, 2.0G, not 2 cores, 2.0G: here's cap is 1 cores"
  eq (← claim t ["run", "--cores", "2", "--", "true"]).code 255

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
  ("test_claim_run_wait_line_names_what_the_head_waits_on", test_claim_run_wait_line_names_what_the_head_waits_on),
  ("test_claim_reserve_and_the_one_machine_view", test_claim_reserve_and_the_one_machine_view),
  ("test_claim_run_all_is_exclusive_and_refuses_mem", test_claim_run_all_is_exclusive_and_refuses_mem),
  ("test_claim_run_short_of_memory_by_unclaimed_use", test_claim_run_short_of_memory_by_unclaimed_use),
  ("test_claim_run_defaulted_cores_over_the_cap_are_lowered", test_claim_run_defaulted_cores_over_the_cap_are_lowered)]

end Claims.Tests.Cli

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
  eq (splitlines (← claim t ["op", "here", "ls"]).stdout).head! "8 0.00 16777216 16777216 8 16777216 0"
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

def tests : List Case := [
  ("test_claim_help", test_claim_help),
  ("test_claim_show_and_op_outside_a_repo", test_claim_show_and_op_outside_a_repo),
  ("test_claim_cap_off_on", test_claim_cap_off_on),
  ("test_claim_run_holds_the_claim_while_it_runs", test_claim_run_holds_the_claim_while_it_runs),
  ("test_claim_run_exits_with_the_commands_code", test_claim_run_exits_with_the_commands_code),
  ("test_claim_run_nothing_fits_is_255", test_claim_run_nothing_fits_is_255)]

end Claims.Tests.Cli

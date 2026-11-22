import ClaimTests.Harness

/-! The ledger script against a scratch XDG_STATE_HOME (moved from swarm's Tests/Cli/Compute.lean; the fixture's machine is an
idle 8-core, 16G one). -/

namespace Claims.Tests.Script
open Claims Claims.Tests

def now (t : T) : IO Int := return (strip (← t.exec ["date", "+%s"]).stdout).toInt!

/-- `try` of `cores` and 1 MiB expecting `est` seconds (`-`: no estimate) as holder `holder`, its one-line answer. -/
def try_ (t : T) (st id cores : String) (est := "-") (holder := "t") : IO String :=
  return strip (← t.scr st ["try", id, cores, "1024", est, holder, "w", "cmd"]).stdout

/-- The ledger dir under `st`. -/
def led (st : String) : String := st ++ "/swarm-compute"

/-- The claim lines `ls` shows, and the ticket lines. -/
def lsRows (t : T) (st : String) (tag : String) : IO (List String) :=
  return (splitlines (← t.scr st ["ls"]).stdout).filter (·.startsWith (tag ++ " "))

def test_script_50_parallel_grant_exactly_4 (t : T) : IO Unit := do
  let st := t.d ++ "/s1"
  discard <| t.scr st ["cap", "8", "-"]
  -- one sh starts the 50: as many Lean tasks each spawning, a CI runner's worker could fork no more (ENOMEM)
  let out := t.d ++ "/s1-answers"
  mkdir out
  discard <| t.exec ["sh", "-c", "k=0; while [ $k -lt 50 ]; do sh -c \"$1\" sh try c$k 2 1024 - t w cmd >\"$2/$k\" 2>\"$2/$k.err\" & k=$((k + 1)); done; wait",
    "sh", SCRIPT, out] [("XDG_STATE_HOME", some st)]
  let rs ← (List.range 50).mapM fun k => return strip ((← slurp s!"{out}/{k}").getD "")
  let errs ← (List.range 50).mapM fun k => return strip ((← slurp s!"{out}/{k}.err").getD "")
  eq (rs.filter (·.startsWith "ok")).length 4 s!"grants; answers {rs.eraseDups}; stderr {(errs.filter (· ≠ "")).eraseDups}"
  eq ((splitlines (← t.scr st ["ls"]).stdout).filter (·.startsWith "c ")).length 4

/-- A stale lock (dead pid, a year 2020 mtime) and 50 `--cores all` claims at once: one wins. -/
def test_script_50_stale_lock_one_winner (t : T) : IO Unit := do
  let st := t.d ++ "/s6"
  let dead := strip (← t.exec ["sh", "-c", "echo $$"]).stdout
  mkdir (led st ++ "/lock")
  put (led st ++ "/lock/pid") s!"{dead}\n"
  discard <| t.exec ["touch", "-t", "202001010000", led st ++ "/lock"]
  let out := t.d ++ "/s6-answers"
  mkdir out
  -- each waits on `go`, so all 50 meet the stale lock together
  let t0 ← IO.monoMsNow
  discard <| t.exec ["sh", "-c", "k=0; while [ $k -lt 50 ]; do (while [ ! -e \"$2/go\" ]; do :; done; sh -c \"$1\" sh try c$k all 1024 - t w cmd >\"$2/$k\" 2>\"$2/$k.err\") & k=$((k + 1)); done; sleep 1; : > \"$2/go\"; wait",
    "sh", SCRIPT, out] [("XDG_STATE_HOME", some st)]
  let ms := (← IO.monoMsNow) - t0
  let rs ← (List.range 50).mapM fun k => return strip ((← slurp s!"{out}/{k}").getD "")
  let errs ← (List.range 50).mapM fun k => return strip ((← slurp s!"{out}/{k}.err").getD "")
  -- the ledger as the 50 left it, before `ls` cleans it: claims, tickets, a lock or break left behind
  let left ← t.exec ["sh", "-c", "cd \"$1\" || exit 1; for f in claims/* claims/.[!.]* queue/* lock lock/pid break break/pid; do if [ -f \"$f\" ]; then printf '%s: %s\\n' \"$f\" \"$(cat \"$f\")\"; elif [ -d \"$f\" ]; then echo \"$f/\"; fi; done",
    "sh", led st]
  let byK (xs : List String) := "; ".intercalate (((List.range 50).zip xs).filterMap fun (k, x) => if x.isEmpty then none else some s!"{k}: {x}")
  let seen := s!"the 50 took {ms} ms\n  answers {byK rs}\n  stderr {byK errs}\n  left {(strip left.stdout).replace "\n" "\n    "}"
  eq (rs.filter (·.startsWith "ok")).length 1 s!"grants; {seen}"
  eq ((splitlines (← t.scr st ["ls"]).stdout).filter (·.startsWith "c ")).length 1 s!"claims; {seen}"

/-- A reading left empty (a `date` or `awk` whose fork failed) ends the try with no answer, and the lock is freed. -/
def test_script_a_failed_reading_grants_nothing (t : T) : IO Unit := do
  let st := t.d ++ "/s7"
  mkdir (t.d ++ "/nodate")
  put (t.d ++ "/nodate/date") "#!/bin/sh\nexit 1\n"
  discard <| t.exec ["chmod", "+x", t.d ++ "/nodate/date"]
  let path := (← IO.getEnv "PATH").getD ""
  let r ← t.scr st ["try", "a", "1", "1024", "-", "t", "w", "cmd"] [("PATH", some (t.d ++ "/nodate:" ++ path))]
  eq r.code 1; eq r.stdout ""
  let r ← t.scr st ["try", "b", "1", "1024", "-", "t", "w", "cmd"] [("SWARM_COMPUTE_BUSY", some "x")]
  eq r.code 1; eq r.stdout ""
  eq (← try_ t st "c" "1") "ok 1 1024"
  eq ((← lsRows t st "c").map fun l => (words l).take 3) [["c", "1", "1024"]]

def test_script_dead_claims_are_not_counted (t : T) : IO Unit := do
  let st := t.d ++ "/s2"
  let dead := strip (← t.exec ["sh", "-c", "echo $$"]).stdout
  mkdir (st ++ "/swarm-compute/claims")
  put (st ++ "/swarm-compute/claims/a") s!"8 1024 p{dead} 1 w x\n"
  put (st ++ "/swarm-compute/claims/b") "8 1024 t1 1 w x\n"
  eq (← try_ t st "n" "8") "ok 8 1024"
  eq (← exists_ (st ++ "/swarm-compute/claims/a")) false
  eq (← exists_ (st ++ "/swarm-compute/claims/b")) false

def test_script_an_old_lock_without_a_live_holder_is_broken (t : T) : IO Unit := do
  let st := t.d ++ "/s5"
  let dead := strip (← t.exec ["sh", "-c", "echo $$"]).stdout
  mkdir (st ++ "/swarm-compute/lock")
  put (st ++ "/swarm-compute/lock/pid") s!"{dead}\n"
  discard <| t.exec ["touch", "-t", "202001010000", st ++ "/swarm-compute/lock"]
  eq (← try_ t st "a" "1") "ok 1 1024"
  -- one whose holder died before writing its pid
  mkdir (st ++ "/swarm-compute/lock")
  discard <| t.exec ["touch", "-t", "202001010000", st ++ "/swarm-compute/lock"]
  eq (← try_ t st "b" "1") "ok 1 1024"
  -- one whose holder died with its pid file made and empty
  mkdir (st ++ "/swarm-compute/lock")
  put (st ++ "/swarm-compute/lock/pid") ""
  discard <| t.exec ["touch", "-t", "202001010000", st ++ "/swarm-compute/lock"]
  eq (← try_ t st "c" "1") "ok 1 1024"

def test_script_older_ticket_holds_back_younger (t : T) : IO Unit := do
  let st := t.d ++ "/s3"
  mkdir (st ++ "/swarm-compute/queue")
  put (st ++ "/swarm-compute/queue/old") s!"{(← now t) - 5} 8 1024 w\n"
  has (← try_ t st "young" "1") "wait 8 16777216 1"
  eq (← try_ t st "old" "8") "ok 8 1024"
  -- the old one is served; the young one's ticket stays until it is granted or dropped
  eq (← try_ t st "young" "1") "wait 0 16776192 0"
  discard <| t.scr st ["drop", "old"]
  eq (← try_ t st "young" "1") "ok 1 1024"
  eq (← exists_ (st ++ "/swarm-compute/queue/young")) false

def test_script_never_off_and_bad_size (t : T) : IO Unit := do
  let st := t.d ++ "/s4"
  discard <| t.scr st ["cap", "4", "-"]
  eq (← try_ t st "big" "5") "never 4 16777216"
  discard <| t.scr st ["off"]
  eq (← try_ t st "x" "1") "off"
  discard <| t.scr st ["on"]
  eq (← try_ t st "one" "2") "ok 2 1024"
  -- `=` keeps a field of the cap
  discard <| t.scr st ["cap", "=", "2048"]
  eq (strip (← t.scr st ["ls"]).stdout |> splitlines |>.head!) "8 0.00 16777216 16777216 4 2048 0 0 0"
  -- no cores, a negative or a word for the estimate
  let r ← t.scr st ["try", "z", "0", "1024", "-", "t", "w", "cmd"]
  eq r.code 2; has r.stderr "bad size"
  eq (← t.scr st ["try", "z", "1", "1024", "soon", "t", "w", "cmd"]).code 2

def test_script_exclusive_all (t : T) : IO Unit := do
  let st := t.d ++ "/x1"
  eq (← try_ t st "one" "2") "ok 2 1024"
  eq (← try_ t st "every" "all") "wait 6 16776192 0"
  -- its ticket says all 0; a later 1-core request is held back by neither the claim nor the ticket's size
  let q ← lsRows t st "q"
  eq q.length 1; has (q.head!) " all 0 w"
  discard <| t.scr st ["drop", "one"]
  eq (← try_ t st "every" "all") "ok 8 16777216"
  has (← lsRows t st "c").head! "8 16777216 t"
  eq (← lsRows t st "q").length 0
  -- nothing else fits beside it
  has (← try_ t st "more" "1") "wait 0"
  -- under a cap below the machine it never runs
  discard <| t.scr st ["drop", "every"]
  discard <| t.scr st ["cap", "4", "-"]
  eq (← try_ t st "every" "all") "never 4 16777216"

def test_script_backfill (t : T) : IO Unit := do
  let st := t.d ++ "/b1"
  mkdir (led st ++ "/queue")
  eq (← try_ t st "run" "6" "90") "ok 6 1024"
  put (led st ++ "/queue/head") s!"{(← now t) - 5} 8 1024 w\n"
  -- it ends in 90 s and the head cannot start before: 200 s past it is a delay, no estimate is no promise
  has (← try_ t st "slow" "2" "200") "wait 2 16776192 1"
  has (← try_ t st "none" "2") "wait 2 16776192 "
  eq (← try_ t st "quick" "2" "50") "ok 2 1024"
  let c ← lsRows t st "c"
  eq c.length 2
  eq (c.filter (subIn · " ~50 w cmd")).length 1
  eq (c.filter (subIn · " ~90 w cmd")).length 1

def test_script_an_old_claim_without_an_estimate_blocks_only_a_head_that_needs_its_cores (t : T) : IO Unit := do
  let st := t.d ++ "/b2"
  mkdir (led st ++ "/claims"); mkdir (led st ++ "/queue")
  let n ← now t
  -- a 6-core claim from before estimates, and an 8-core head: the head's start is unknown
  put (led st ++ "/claims/old") s!"6 1024 t{n + 100000} {n} w x\n"
  put (led st ++ "/queue/head") s!"{n - 5} 8 1024 w\n"
  has (← try_ t st "r" "2" "50") "wait"
  -- a 2-core one and a 4-core one with an estimate: the 4-core head needs room the estimated claim gives back
  let st := t.d ++ "/b3"
  mkdir (led st ++ "/claims"); mkdir (led st ++ "/queue")
  put (led st ++ "/claims/old") s!"2 1024 t{n + 100000} {n} w x\n"
  put (led st ++ "/claims/est") s!"4 1024 t{n + 100000} {n} ~90 w x\n"
  put (led st ++ "/queue/head") s!"{n - 5} 4 1024 w\n"
  eq (← try_ t st "r" "2" "50") "ok 2 1024"

def test_script_reserve (t : T) : IO Unit := do
  let st := t.d ++ "/r1"
  discard <| t.scr st ["reserve", "4", "0"]
  -- 6 cores wait for the user (held); a younger 2-core request runs past it, with no estimate
  has (← try_ t st "big" "6") "wait 4 "
  eq (← try_ t st "small" "2") "ok 2 1024"
  eq (strip (← t.scr st ["ls"]).stdout |> splitlines |>.head!) "8 0.00 16777216 16777216 8 16777216 0 4 0"
  discard <| t.scr st ["reserve", "0", "0"]
  eq (← try_ t st "big" "6") "ok 6 1024"
  -- the cap and the reservation are separate files
  let st := t.d ++ "/r2"
  discard <| t.scr st ["cap", "6", "-"]
  discard <| t.scr st ["reserve", "4", "0"]
  discard <| t.scr st ["reserve", "0", "0"]
  eq (strip (← readF [led st, "cap"])) "6 -"
  eq (← exists_ (led st ++ "/reserve")) false
  -- a reservation larger than the machine is clamped when shown
  discard <| t.scr st ["reserve", "20", "999999999999"]
  has (← t.scr st ["ls"]).stdout " 0 8 16777216\n"
  eq (← t.scr st ["reserve", "x", "0"]).code 2

def test_script_an_exclusive_head_keeps_its_place_through_unclaimed_use_then_yields (t : T) : IO Unit := do
  let st := t.d ++ "/h1"
  -- 4 busy cores that no claim explains: 3 past the noise floor
  let env (now : Nat) : List (String × Option String) := [("SWARM_COMPUTE_BUSY", some "4.00"), ("SWARM_COMPUTE_NOW", some (toString now))]
  let try2 (now : Nat) (id cores : String) (est := "-") : IO String :=
    return strip (← t.scr st ["try", id, cores, "1024", est, "t", "w", "cmd"] (env now)).stdout
  -- `ls` at the test's clock: the real one would sweep its claims
  let ticket (now : Nat) (id : String) : IO String := do
    return ((splitlines (← t.scr st ["ls"] (env now)).stdout).find? (·.startsWith s!"q {id} ")).getD ""
  eq (← try2 5000 "bench" "all") "wait 5 16777216 0"
  -- no claim, and unclaimed use keeps it off: its clock starts
  eq (← ticket 5000 "bench") "q bench 5000 all 0 @5000 w"
  -- it keeps its place: no estimate waits, and with no claim its shadow is now, so no estimate is short enough
  eq (← try2 5000 "small" "2") "wait 5 16777216 1"
  eq (← try2 5000 "quick" "2" "50") "wait 5 16777216 1"
  -- its own tries keep the clock
  eq (← try2 5300 "bench" "all") "wait 5 16777216 0"
  eq (← ticket 5300 "bench") "q bench 5000 all 0 @5000 w"
  -- ten minutes on it has yielded: held, so it blocks no one (the oldest waiter behind it runs)
  eq (← try2 5600 "quick" "2" "50") "ok 2 1024"
  -- a claim is live: the clock stops, and it is a head again
  eq (← try2 5601 "bench" "all") "wait 5 16776192 0"
  eq (← ticket 5601 "bench") "q bench 5000 all 0 w"
  eq (← try2 5601 "tiny" "1") "wait 5 16776192 2"
  has (← t.scr st ["ls"] (env 5601)).stdout " 5600 ~50 w cmd"



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

def notes (t : T) (st : String) (now : Int) : IO (List String) :=
  return (splitlines (← t.scr st ["ls"] [("SWARM_COMPUTE_NOW", some (toString now))]).stdout).filter (·.startsWith "n ")

def test_script_notes_add_renew_rm_and_lapse (t : T) : IO Unit := do
  let st := t.d ++ "/n1"
  let atT (k : Int) (args : List String) : IO R := t.scr st args [("SWARM_COMPUTE_NOW", some (toString k))]
  eq (← atT 1000 ["qadd", "tq-1", "tq", "hpl-1", "1200", "600", "-", "timing run"]).code 0
  eq (← notes t st 1000) ["n t1600 1200 1000 hpl-1 tq timing run"]
  -- a renewal moves the expiry, keeps the first sight
  eq (← atT 1300 ["qadd", "tq-1", "tq", "hpl-1", "1200", "600", "-", "timing run"]).code 0
  eq (← notes t st 1300) ["n t1900 1200 1000 hpl-1 tq timing run"]
  -- no estimate, the owner defaulting to the user
  eq (← atT 1300 ["qadd", "b", "-", "x", "-", "100", "-", "c"]).code 0
  eq ((← notes t st 1300).map (·.splitOn " " |>.drop 3 |>.take 1)) [["1300"], ["1000"]]
  -- it holds no cores and no place in line
  -- it lapses with its ttl, the renewed one later than the other
  eq (← notes t st 1450).length 1
  eq (← notes t st 1900).length 0
  eq (← exists_ (led st ++ "/notes/tq-1")) false
  -- rm, and bad arguments
  discard <| atT 2000 ["qadd", "r", "o", "w", "-", "100", "-", "c"]
  discard <| t.scr st ["qrm", "r"]
  eq (← notes t st 2000).length 0
  eq (← atT 2000 ["qadd", "../x", "o", "w", "-", "100", "-", "c"]).code 2
  eq (← atT 2000 ["qadd", "r", "o", "w", "x", "100", "-", "c"]).code 2
  eq (← atT 2000 ["qadd", "r", "o", "w", "-", "0", "-", "c"]).code 2
  -- (real clock from here: it would sweep the fake-dated notes)
  discard <| t.scr st ["qadd", "live", "o", "w", "-", "600", "-", "c"]
  eq (← try_ t st "j" "8") "ok 8 1024"
  eq (← lsRows t st "q") []
  eq (← lsRows t st "n").length 1
  discard <| t.scr st ["qrm", "live"]

def test_script_a_note_with_a_pid_is_swept_when_it_is_gone (t : T) : IO Unit := do
  let st := t.d ++ "/n2"
  let dead := strip (← t.exec ["sh", "-c", "echo $$"]).stdout
  let live := strip (← t.exec ["sh", "-c", "echo $PPID"]).stdout
  -- the long ttl does not matter with a pid
  discard <| t.scr st ["qadd", "gone", "o", "w", "-", "1", dead, "c"]
  discard <| t.scr st ["qadd", "here", "o", "w", "-", "1", live, "c"]
  let rows := (splitlines (← t.scr st ["ls"]).stdout).filter (·.startsWith "n ")
  eq rows.length 1; has rows.head! s!"n p{live} "
  eq (← exists_ (led st ++ "/notes/gone")) false

/-- `hold` (board #109): the claim's holder becomes a pid, its other fields kept. A remote claim (holder `t`) is held 15
minutes from its grant: a job that starts later (a long sync) finds it lapsed, and `hold` fails, as for a claim whose
holder died or one never made. -/
def test_script_hold_moves_the_holder_and_fails_on_a_lapsed_claim (t : T) : IO Unit := do
  let st := t.d ++ "/hd"
  let env (now : Nat) : List (String × Option String) := [("SWARM_COMPUTE_BUSY", some "0.00"), ("SWARM_COMPUTE_NOW", some (toString now))]
  let live := strip (← t.exec ["sh", "-c", "echo $PPID"]).stdout
  let dead := strip (← t.exec ["sh", "-c", "echo $$"]).stdout
  let claim (id : String) : IO String := return strip ((← slurp (led st ++ "/claims/" ++ id)).getD "")
  eq (strip (← t.scr st ["try", "r", "1", "1024", "60", "t", "w", "a b  c"] (env 1000)).stdout) "ok 1 1024"
  eq (← claim "r") "1 1024 t1900 1000 ~60 w a b  c"
  -- the job starts within the 15 minutes: its pid holds the claim, past them too
  eq (← t.scr st ["hold", "r", live] (env 1899)).code 0
  eq (← claim "r") s!"1 1024 p{live} 1000 ~60 w a b  c"
  discard <| t.scr st ["ls"] (env 5000)
  eq (← claim "r") s!"1 1024 p{live} 1000 ~60 w a b  c"
  -- the job starts after them: the claim lapsed, the job is told
  eq (strip (← t.scr st ["try", "s", "1", "1024", "-", "t", "w", "c"] (env 1000)).stdout) "ok 1 1024"
  let r ← t.scr st ["hold", "s", live] (env 1901)
  eq r.code 3; has r.stderr "no claim s"
  eq (← exists_ (led st ++ "/claims/s")) false
  -- a claim whose holder died (a detached run's parent), and one never made
  put (led st ++ "/claims/d") s!"1 1024 p{dead} 1000 w c\n"
  eq (← t.scr st ["hold", "d", live]).code 3
  eq (← exists_ (led st ++ "/claims/d")) false
  eq (← t.scr st ["hold", "none", live]).code 3
  eq (← t.scr st ["hold", "../x", live]).code 2
  eq (← t.scr st ["hold", "r", "x"]).code 2
  eq (← claim "r") s!"1 1024 p{live} 1000 ~60 w a b  c"

/-- `hold <id> t` (board #126): a timed claim's 15 minutes start again, so a long sync keeps a remote claim; a lapsed
claim is not renewed, and a pid's claim is kept as it is. -/
def test_script_hold_t_renews_a_timed_claim_and_fails_on_a_lapsed_one (t : T) : IO Unit := do
  let st := t.d ++ "/ht"
  let env (now : Nat) : List (String × Option String) := [("SWARM_COMPUTE_BUSY", some "0.00"), ("SWARM_COMPUTE_NOW", some (toString now))]
  let live := strip (← t.exec ["sh", "-c", "echo $PPID"]).stdout
  let claim (id : String) : IO String := return strip ((← slurp (led st ++ "/claims/" ++ id)).getD "")
  eq (strip (← t.scr st ["try", "r", "1", "1024", "60", "t", "w", "a b  c"] (env 1000)).stdout) "ok 1 1024"
  eq (← claim "r") "1 1024 t1900 1000 ~60 w a b  c"
  -- renewed within the 15 minutes: they start again, the other fields kept
  eq (← t.scr st ["hold", "r", "t"] (env 1800)).code 0
  eq (← claim "r") "1 1024 t2700 1000 ~60 w a b  c"
  -- past the first expiry it still holds
  discard <| t.scr st ["ls"] (env 2000)
  eq (← claim "r") "1 1024 t2700 1000 ~60 w a b  c"
  -- the job's pid then holds it, and a late renewal leaves the pid
  eq (← t.scr st ["hold", "r", live] (env 2600)).code 0
  eq (← t.scr st ["hold", "r", "t"] (env 2650)).code 0
  eq (← claim "r") s!"1 1024 p{live} 1000 ~60 w a b  c"
  -- a lapsed claim is not renewed
  eq (strip (← t.scr st ["try", "s", "1", "1024", "-", "t", "w", "c"] (env 1000)).stdout) "ok 1 1024"
  let r ← t.scr st ["hold", "s", "t"] (env 1901)
  eq r.code 3; has r.stderr "no claim s"
  eq (← exists_ (led st ++ "/claims/s")) false

def tests : List Case := [
  ("test_script_notes_add_renew_rm_and_lapse", test_script_notes_add_renew_rm_and_lapse),
  ("test_script_a_note_with_a_pid_is_swept_when_it_is_gone", test_script_a_note_with_a_pid_is_swept_when_it_is_gone),
  ("test_script_50_parallel_grant_exactly_4", test_script_50_parallel_grant_exactly_4),
  ("test_script_a_failed_reading_grants_nothing", test_script_a_failed_reading_grants_nothing),
  ("test_script_dead_claims_are_not_counted", test_script_dead_claims_are_not_counted),
  ("test_script_an_old_lock_without_a_live_holder_is_broken", test_script_an_old_lock_without_a_live_holder_is_broken),
  ("test_script_older_ticket_holds_back_younger", test_script_older_ticket_holds_back_younger),
  ("test_script_never_off_and_bad_size", test_script_never_off_and_bad_size),
  ("test_script_exclusive_all", test_script_exclusive_all),
  ("test_script_backfill", test_script_backfill),
  ("test_script_an_old_claim_without_an_estimate_blocks_only_a_head_that_needs_its_cores", test_script_an_old_claim_without_an_estimate_blocks_only_a_head_that_needs_its_cores),
  ("test_script_reserve", test_script_reserve),
  ("test_script_an_exclusive_head_keeps_its_place_through_unclaimed_use_then_yields", test_script_an_exclusive_head_keeps_its_place_through_unclaimed_use_then_yields),
  ("test_script_compute_dir_overrides_the_ledger", test_script_compute_dir_overrides_the_ledger),
  ("test_script_arithmetic_of_the_awk_programs", test_script_arithmetic_of_the_awk_programs),
  ("test_script_hold_moves_the_holder_and_fails_on_a_lapsed_claim", test_script_hold_moves_the_holder_and_fails_on_a_lapsed_claim),
  ("test_script_hold_t_renews_a_timed_claim_and_fails_on_a_lapsed_one", test_script_hold_t_renews_a_timed_claim_and_fails_on_a_lapsed_one)]

end Claims.Tests.Script

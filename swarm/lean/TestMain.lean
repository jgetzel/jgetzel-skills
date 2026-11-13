import Tests.Cli.All

/-! swarm-tests: the CLI's test suite (run.lua's runner). `swarm-tests [pattern]` runs every test whose spec or name
contains the pattern, one worker process per test, SWARM_TEST_JOBS (8) at a time; a test running past
SWARM_TEST_TIMEOUT (60 s) is killed and reported as HUNG. `--list` prints the tests; `--one <spec> <test>` is a worker;
`--fake-launch` and `--sql` are the fakes the fixture writes as scripts; `--sqlite` is sqlite_spec's worker. -/

open SwarmLean SwarmLean.Tests.Cli

/-- Every test, as (spec, name, body). -/
def all : List (String × String × (T → IO Unit)) :=
  specs.flatMap fun (s, cs) => cs.map fun (n, f) => (s, n, f)

/-- A worker: runs one test on a fresh fixture. -/
def one (spec name : String) : IO UInt32 := do
  let some (_, _, f) := all.find? fun (s, n, _) => s == spec && n == name
    | IO.eprintln s!"no test {spec} {name}"; return 1
  let t ← T.new
  let err ← try f t; pure none catch e => pure (some (toString e))
  t.cleanup err.isNone
  match err with
  | none => return 0
  | some e => IO.eprintln s!"{e}\n  (fixture kept: {t.d})"; return 1

/-- A number from the environment, else the default. -/
def envNat (k : String) (d : Nat) : IO Nat := return ((← IO.getEnv k).bind String.toNat?).getD d

/-- The coordinator. -/
def coordinate (pat : Option String) : IO UInt32 := do
  let timeout ← envNat "SWARM_TEST_TIMEOUT" 60
  let jobsMax ← envNat "SWARM_TEST_JOBS" 8
  let jobs := (all.filter fun (s, n, _) => match pat with
    | some p => subIn s p || subIn n p | none => true).toArray
  let tmp := strip (← IO.Process.output { cmd := "mktemp", args := #["-d"] }).stdout
  let self ← selfBin
  let mut running : Array (Nat × IO.Process.Child ⟨.null, .null, .null⟩ × Nat) := #[]
  let mut rcs : Array (Option UInt32) := Array.replicate jobs.size none
  let mut next := 0
  let mut done := 0
  while done < jobs.size do
    while running.size < jobsMax && next < jobs.size do
      let (s, n, _) := jobs[next]!
      let args := #["-c", "exec \"$0\" --one \"$1\" \"$2\" >\"$3\" 2>&1", self, s, n, s!"{tmp}/{next}.out"]
      let c ← IO.Process.spawn { cmd := "sh", args, stdin := .null, stdout := .null, stderr := .null }
      running := running.push (next, c, (← IO.monoMsNow))
      next := next + 1
    let mut still := #[]
    for (i, c, t0) in running do
      match ← c.tryWait with
      | some rc => rcs := rcs.set! i (some rc); done := done + 1
      | none =>
        if (← IO.monoMsNow) - t0 > timeout * 1000 then
          c.kill; discard c.wait
          rcs := rcs.set! i (some 137); done := done + 1
        else still := still.push (i, c, t0)
    running := still
    IO.sleep 50
  let mut failed := 0
  for h : i in [0:jobs.size] do
    let (s, n, _) := jobs[i]
    let rc := rcs[i]!.getD 1
    if rc == 0 then IO.println s!"ok    {s} {n}"
    else
      failed := failed + 1
      let out := (← slurp s!"{tmp}/{i}.out").getD ""
      let out := if rc == 137 then s!"HUNG: killed after {timeout}s with no result\n{out}" else out
      IO.println s!"FAIL  {s} {n}\n{out}"
  discard <| IO.Process.output { cmd := "rm", args := #["-rf", tmp] }
  IO.println s!"{jobs.size} run, {failed} failed"
  return if failed == 0 && jobs.size > 0 then 0 else 1

def main (args : List String) : IO UInt32 := do
  match args with
  | "--fake-launch" :: d :: argv => T.fakeLaunch d argv
  | "--sqlite" :: role :: rest => SwarmLean.Tests.Spec.Sqlite.worker role rest
  | ["--sql", db, stmt] => discard <| (← SwarmLean.Sqlite.Conn.open db false).exec stmt; return 0
  | ["--one", s, n] => one s n
  | ["--list"] => for (s, n, _) in all do IO.println s!"{s} {n}"
                  return 0
  | [p] => coordinate (some p)
  | [] => coordinate none
  | _ => IO.eprintln "usage: swarm-tests [pattern] | --list"; return 2

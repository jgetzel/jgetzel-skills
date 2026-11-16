import Claims.Ledger

/-! claim-tests' own small harness: a scratch dir per test, `sh` and `claim` run against it, compare. The ledger reads a
fixed idle 8-core, 16G machine (SWARM_COMPUTE_STAT/_MEM), as swarm's fixture's. -/

namespace Claims.Tests

structure R where
  stdout : String
  stderr : String
  code : Int

/-- A test's scratch dir. -/
structure T where
  d : String

abbrev Case := String × (T → IO Unit)

def fail {α} (msg : String) : IO α := throw <| IO.userError msg

def subIn (s sub : String) : Bool := sub.isEmpty || (s.splitOn sub).length > 1

def eq [BEq α] [Repr α] (got want : α) (msg := "not equal") : IO Unit :=
  unless got == want do fail s!"{msg}\n  got  {repr got}\n  want {repr want}"

def has (s sub : String) : IO Unit := unless subIn s sub do fail s!"missing {sub.quote}\n  in {s.quote}"

def hasnt (s sub : String) : IO Unit := if subIn s sub then fail s!"unexpected {sub.quote}\n  in {s.quote}" else pure ()

def put (p text : String) : IO Unit := IO.FS.writeFile p text

def mkdir (p : String) : IO Unit := IO.FS.createDirAll p

def exists_ (p : String) : IO Bool := System.FilePath.pathExists p

def slurp (p : String) : IO (Option String) := do try return some (← IO.FS.readFile p) catch _ => return none

def readF (parts : List String) : IO String := IO.FS.readFile ("/".intercalate parts)

namespace T

/-- Runs `argv` in the test's dir (or `cwd`) with the fixed machine readings and `env` on top. -/
def exec (t : T) (argv : List String) (env : List (String × Option String) := []) (cwd : Option String := none)
    (input : Option String := none) : IO R := do
  -- an input is a file the command reads on stdin
  let argv ← match input with
    | some s => do put (t.d ++ "/stdin") s; pure (["sh", "-c", "exec \"$@\" <\"$0\"", t.d ++ "/stdin"] ++ argv)
    | none => pure argv
  let some cmd := argv.head? | fail "no command"
  let path := (← IO.getEnv "PATH").getD ""
  let env := [("PATH", some (t.d ++ "/bin:" ++ path)), ("SWARM_COMPUTE_STAT", some (t.d ++ "/stat")), ("SWARM_COMPUTE_MEM", some (t.d ++ "/meminfo")),
    ("SWARM_COMPUTE_POLL_MS", some "200"), ("XDG_STATE_HOME", some (t.d ++ "/.state"))] ++ env
  let child ← IO.Process.spawn { cmd := cmd, args := argv.tail.toArray, env := env.toArray, cwd := (cwd.map System.FilePath.mk), stdin := .null, stdout := .piped, stderr := .piped }
  let errT ← IO.asTask child.stderr.readToEnd
  let out ← child.stdout.readToEnd
  let err ← IO.ofExcept (← IO.wait errT)
  return { stdout := out, stderr := err, code := (← child.wait).toNat }

/-- The script's op against the ledger under `st` (XDG_STATE_HOME). -/
def scr (t : T) (st : String) (args : List String) (env : List (String × Option String) := []) : IO R :=
  t.exec (["sh", "-c", SCRIPT, "sh"] ++ args) ([("XDG_STATE_HOME", some st)] ++ env)

/-- A fresh test dir. -/
def new : IO T := do
  let r ← IO.Process.output { cmd := "mktemp", args := #["-d", s!"{(← IO.getEnv "TMPDIR").getD "/tmp"}/claim-test-XXXXXX"] }
  if r.exitCode ≠ 0 then fail s!"mktemp: {r.stderr}"
  let d := (← IO.FS.realPath (strip r.stdout)).toString
  mkdir (d ++ "/.state")
  -- no hc: the machines are `here` alone
  mkdir (d ++ "/bin")
  put (d ++ "/bin/hc") "#!/bin/sh\necho '{}'\n"
  discard <| IO.Process.output { cmd := "chmod", args := #["+x", d ++ "/bin/hc"] }
  put (d ++ "/stat") ("cpu  0 0 0 800 0 0 0 0 0 0\n" ++ "".intercalate ((List.range 8).map fun i => s!"cpu{i} 0 0 0 100 0 0 0 0 0 0\n"))
  put (d ++ "/meminfo") "MemTotal:       16777216 kB\nMemAvailable:   16777216 kB\n"
  return { d }

/-- Removes the dir when the test passed. -/
def cleanup (t : T) (passed : Bool) : IO Unit :=
  if passed then discard <| IO.Process.output { cmd := "rm", args := #["-rf", t.d] } else pure ()

end T
end Claims.Tests

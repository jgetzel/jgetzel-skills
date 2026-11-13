import Lean.Data.Json
import SwarmLean.RealSys

/-! The CLI test fixture, cli.lua's in Lean. A spec file `Tests/Cli/<Spec>.lean` ends in `def tests : List Case`, each a
named test run with a fresh fixture `t` by the `swarm-tests` executable (TestMain.lean), which reports failures by name.

Fixture fields: `t.d` (temp dir), `t.repo` (git repo on main: a.txt b.txt "x", e.txt "mod (p, q)\n"), `t.wt` (worktree
on branch w2), `t.db`; `t.cwdOf who` ({a = repo, b = wt}; `t.setCwd` adds more), `t.fakebin` and `t.launch` (set by
fakes/liveHc/fake).
Running things (`R`: stdout, stderr, code):
- `t.sw who args o` (`t.sw_` discards the result)  swarm as SWARM_NAME=who in t.cwd[who] (else t.repo); `o`: ok (default true: asserts code 0), stdin,
  hc (HC_TERMINAL_ID; unset otherwise), cwd, env (extra vars, none unsets)
- `t.hook who ev payload hc`  swarm hook <ev> with payload as JSON (cwd defaults); hookSpecificOutput or {}
- `t.edit who path`  pre-tool Edit of t.cwd[who]/path
- `t.exec argv o`  any command (proc.exec opts); `t.git cwd args` git as user t, asserting success
Db: `t.q sql ps` (`t.q_` for its effect) rows as JSON objects keyed by column name (NULL is absent: alias count(*) etc.), `t.q1` the first row
(null when none), `t.agent name cols` joins then sets columns.
Files and conflicts: `t.write who path text`, `t.tick` (watchd --once), `t.notices who`, `t.land path text`.
Fakes: `t.fakes` puts fake hc, gh and launch script in place; `t.setHc terminals` (none: hc ls fails), `t.setGh sub out`
(none: gh <sub> fails), `t.calls name` logged argv lines, `t.launched` {argv, task: [[owner, state]...]} per launch,
`t.liveHc addrs` an hc whose ls shows these live, `t.fake name body` any executable in t.fakebin.
Asserts (msg optional): `eq got want` deep (as JSON), `has s sub` / `hasnt s sub` plain substring (or list member).
Cleanup: `t.defer act` runs after the test; the temp dir is removed when the test passes, kept when it fails.

The fakes cli.lua wrote in Lua are the test binary itself: `swarm-tests --fake-launch <dir> argv…` is the launch
script, `swarm-tests --sql <db> <statement>` a write from outside. -/

namespace SwarmLean.Tests.Cli
open Lean (Json ToJson toJson)
open SwarmLean.Sqlite (Val)
open SwarmLean

instance : Coe String Val := ⟨.text⟩
instance : OfNat Val n := ⟨.int n⟩

/-- A command's result. -/
structure R where
  stdout : String
  stderr : String
  code : Int
  deriving Inhabited

/-- t:sw's options. -/
structure Opts where
  ok : Bool := true
  stdin : Option String := none
  hc : Option String := none
  cwd : Option String := none
  env : List (String × Option String) := []

/-- The fixture. -/
structure T where
  d : String
  repo : String
  wt : String
  db : String
  cwds : IO.Ref (List (String × String))
  fakebinR : IO.Ref (Option String)
  launchR : IO.Ref (Option String)
  cleanups : IO.Ref (Array (IO Unit))

/-- A named test. -/
abbrev Case := String × (T → IO Unit)

/-- The directory swarm/: $SWARM_DIR, else the first directory above the binary holding lean/lakefile.lean. -/
def swarmDir : IO String := do
  if let some d ← IO.getEnv "SWARM_DIR" then if d ≠ "" then return d
  let mut p ← IO.appPath
  for _ in [0:12] do
    match p.parent with
    | some q =>
      p := q
      if ← (p / "lean" / "lakefile.lean").pathExists then return (← IO.FS.realPath p).toString
    | none => break
  throw <| IO.userError "swarm/ not found above the test binary: set SWARM_DIR"

/-- The CLI under test: $SWARM_BIN, else the swarm-lean beside the test binary. -/
def swarmBin : IO String := do
  if let some b ← IO.getEnv "SWARM_BIN" then if b ≠ "" then return b
  return ((← IO.appPath).parent.getD "." / "swarm-lean").toString

/-- The test binary (for the fakes that are it). -/
def selfBin : IO String := return (← IO.appPath).toString

/-- PATH as the test process got it. -/
def basePath : IO String := return (← IO.getEnv "PATH").getD ""

/-- XDG_DATA_HOME, else ~/.local/share. -/
def xdg : IO String := do
  if let some x ← IO.getEnv "XDG_DATA_HOME" then return x
  return s!"{(← IO.getEnv "HOME").getD ""}/.local/share"

/-- A failure. -/
def fail {α} (msg : String) : IO α := throw <| IO.userError msg

/-- A plain substring test (the empty string is in every string, as Lua's find). -/
def subIn (s sub : String) : Bool := sub.isEmpty || (s.splitOn sub).length > 1

/-- A value as cli.lua's repr shows it, roughly: compact JSON. -/
def repr (j : Json) : String := j.compress

/-- Deep equality; numbers compare by value (1 and 1.0 alike). -/
partial def deq : Json → Json → Bool
  | .num a, .num b => a.toFloat == b.toFloat
  | .arr a, .arr b => a.size == b.size && (a.zip b).all fun (x, y) => deq x y
  | .obj a, .obj b =>
    let ka := a.toArray; let kb := b.toArray
    ka.size == kb.size && ka.all fun (k, v) => match b.get? k with | some w => deq v w | none => false
  | a, b => a == b

/-- t:eq. -/
def eq [ToJson α] [ToJson β] (got : α) (want : β) (msg := "not equal") : IO Unit := do
  let g := toJson got; let w := toJson want
  unless deq g w do fail s!"{msg}\n  got  {repr g}\n  want {repr w}"

/-- Is `sub` in `s`: a substring of a string, or a member of a list. -/
def hasJ (s sub : Json) : Bool :=
  match s, sub with
  | .str a, .str b => subIn a b
  | .arr xs, x => xs.any (deq · x)
  | _, _ => false

/-- t:has. -/
def has [ToJson α] [ToJson β] (s : α) (sub : β) (msg := "missing") : IO Unit := do
  unless hasJ (toJson s) (toJson sub) do fail s!"{msg}\n  {repr (toJson sub)}\n  not in {repr (toJson s)}"

/-- t:hasnt. -/
def hasnt [ToJson α] [ToJson β] (s : α) (sub : β) (msg := "unexpected") : IO Unit := do
  if hasJ (toJson s) (toJson sub) then fail s!"{msg}\n  {repr (toJson sub)}\n  is in {repr (toJson s)}"

/-- A JSON object's field (null when missing or not an object). -/
def _root_.Lean.Json.f (j : Json) (k : String) : Json := j.getObjValD k

/-- A JSON value's text (Lua's tostring of a string, else the compact JSON; nil for null). -/
def _root_.Lean.Json.s? : Json → Option String
  | .str s => some s
  | .null => none
  | j => some j.compress

/-- A JSON number as an Int (0 when not one). -/
def _root_.Lean.Json.i (j : Json) : Int := (j.getInt?).toOption.getD 0

/-- A JSON array's length (Lua's #). -/
def _root_.Lean.Json.len : Json → Nat
  | .arr a => a.size
  | _ => 0

/-- A file's contents, none when unreadable (util.slurp). -/
def slurp (p : String) : IO (Option String) := do
  try return some (← IO.FS.readFile p) catch _ => return none

/-- Lines without their newlines (util.splitlines). -/
def splitlines (s : String) : List String :=
  let ls := s.splitOn "\n"
  if ls.getLast? == some "" then ls.dropLast else ls

/-- Writes a file, then chmods it when a mode is given. -/
def put (path text : String) (mode : Option String := none) : IO Unit := do
  IO.FS.writeFile path text
  if let some m := mode then discard <| IO.Process.output { cmd := "chmod", args := #[m, path] }

namespace T

/-- The cwd of `who`, if set. -/
def cwdOf? (t : T) (who : String) : IO (Option String) := return (← t.cwds.get).lookup who

/-- The cwd of `who`, else the repo. -/
def cwdOf (t : T) (who : String) : IO String := return (← t.cwdOf? who).getD t.repo

/-- Sets the cwd of `who` (t.cwd.who = dir). -/
def setCwd (t : T) (who dir : String) : IO Unit := t.cwds.modify fun l => (who, dir) :: l.filter (·.1 ≠ who)

/-- The fake bin dir, if fakes made one. -/
def fakebin (t : T) : IO (Option String) := t.fakebinR.get

/-- The launch script's path, if fakes made one. -/
def launch (t : T) : IO String := return (← t.launchR.get).getD ""

/-- t:defer. -/
def defer (t : T) (act : IO Unit) : IO Unit := t.cleanups.modify (·.push act)

/-- t:exec: any command, proc.exec's options. -/
def exec (_ : T) (argv : List String) (o : RunOpts := {}) : IO R := do
  let r ← execIO' argv o
  return { stdout := r.stdout, stderr := r.stderr, code := r.code.toNat }

/-- git as user t in `cwd`, asserting success; its stdout. -/
def git (t : T) (cwd : Option String) (args : List String) : IO String := do
  let r ← t.exec (["git", "-c", "user.name=t", "-c", "user.email=t@t"] ++ args) { cwd }
  if r.code ≠ 0 then fail s!"git {" ".intercalate args}: {r.stderr}"
  return r.stdout

/-- swarm as SWARM_NAME=who. -/
def sw (t : T) (who : String) (args : List String) (o : Opts := {}) : IO R := do
  let bp ← basePath
  let path := match ← t.fakebin with | some fb => s!"{fb}:{bp}" | none => bp
  let mut env : List (String × Option String) :=
    [("SWARM_DB", some t.db), ("SWARM_NAME", some who), ("HC_TERMINAL_ID", o.hc), ("PATH", some path),
     ("XDG_DATA_HOME", some (← xdg))]
  if let some l ← t.launchR.get then env := env ++ [("SWARM_LAUNCH", some l)]
  for (k, v) in o.env do env := (env.filter (·.1 ≠ k)) ++ [(k, v)]
  -- a faked /proc is Linux's layout; macOS reads sysctl, vm_stat and lsof instead
  if (env.lookup "SWARM_PROC").join.isSome && (env.lookup "SWARM_OS").join.isNone then
    env := (env.filter (·.1 ≠ "SWARM_OS")) ++ [("SWARM_OS", some "Linux")]
  let cwd ← match o.cwd with | some c => pure c | none => t.cwdOf who
  let r ← t.exec ((← swarmBin) :: args) { env, input := o.stdin, cwd }
  if o.ok && r.code ≠ 0 then fail s!"swarm {" ".intercalate args} exited {r.code}: {r.stderr}{r.stdout}"
  return r

/-- t.sw for its effect. -/
def sw_ (t : T) (who : String) (args : List String) (o : Opts := {}) : IO Unit := discard <| t.sw who args o

/-- swarm hook <ev> with the payload as JSON; its hookSpecificOutput, or {} when it printed nothing. -/
def hook (t : T) (who ev : String) (payload : Json := Json.mkObj []) (hc : Option String := none) : IO Json := do
  let payload ← if payload.f "cwd" == .null then
      pure (payload.setObjVal! "cwd" (← t.cwdOf who)) else pure payload
  let r ← t.sw who ["hook", ev] { stdin := payload.compress, hc }
  if strip r.stdout == "" then return Json.mkObj []
  match Json.parse r.stdout with
  | .ok j => return j.f "hookSpecificOutput"
  | .error e => fail s!"hook printed no JSON ({e}): {r.stdout}"

/-- A pre-tool Edit of t.cwd[who]/path. -/
def edit (t : T) (who path : String) : IO Json := do
  t.hook who "pre-tool" (Json.mkObj [("tool_name", "Edit"),
    ("tool_input", Json.mkObj [("file_path", s!"{← t.cwdOf who}/{path}")])])

/-- A cell as JSON. -/
def cell : Val → Json
  | .null => .null
  | .int i => toJson i
  | .real f => toJson f
  | .text s => .str s

/-- Rows of `sql` as JSON objects by column name, NULL columns absent (t:q, through db.connect). -/
def q (t : T) (sql : String) (ps : List Val := []) : IO (Array Json) := do
  Shim.setenv "SWARM_DB" t.db
  let c ← connect
  let s ← c.prepare sql
  let mut i : UInt32 := 1
  for p in ps do
    s.bind i p
    i := i + 1
  let n ← s.columnCount
  let mut names := #[]
  for j in [0:n.toNat] do names := names.push (← s.columnName j.toUInt32)
  let mut rows := #[]
  repeat
    let st ← s.stepRaw
    if st == 1 then
      let mut kv := #[]
      for j in [0:n.toNat] do
        let v ← s.column j.toUInt32
        if v != .null then kv := kv.push (names[j]!, cell v)
      rows := rows.push (Json.mkObj kv.toList)
    else if st == 0 then break
    else fail s!"sql: {← c.errmsg}: {sql}"
  return rows

/-- t.q for its effect. -/
def q_ (t : T) (sql : String) (ps : List Val := []) : IO Unit := discard <| t.q sql ps

/-- The first row, null when none. -/
def q1 (t : T) (sql : String) (ps : List Val := []) : IO Json := return (← t.q sql ps)[0]?.getD .null

/-- Joins `name`, then sets its columns. -/
def agent (t : T) (name : String) (cols : List (String × Val) := []) : IO Unit := do
  discard <| t.sw name ["join"]
  for (k, v) in cols do discard <| t.q s!"update agent set {k}=? where name=?" [v, .text name]

/-- Writes t.cwd[who]/path. -/
def write (t : T) (who path text : String) : IO Unit := do put s!"{← t.cwdOf who}/{path}" text

/-- watchd --once. -/
def tick (t : T) : IO Unit := discard <| t.sw "a" ["watchd", "--once"]

/-- Notices to `who`. -/
def notices (t : T) (who : String) : IO (Array Json) := t.q "select body from msg where dest=? and kind='notice'" [.text who]

/-- A peer's PR lands on origin/main and t.repo fetches it. -/
def land (t : T) (path text : String) : IO Unit := do
  let o := t.d ++ "/origin.git"; let pr := t.d ++ "/pr"
  if (← slurp (o ++ "/HEAD")).isNone then
    discard <| t.git none ["clone", "-q", "--bare", t.repo, o]
    discard <| t.git t.repo ["remote", "add", "origin", o]
  discard <| t.git none ["clone", "-q", o, pr]
  put (pr ++ "/" ++ path) text
  discard <| t.git pr ["commit", "-qam", "pr"]
  discard <| t.git pr ["push", "-q", "origin", "main"]
  IO.FS.removeDirAll pr
  discard <| t.git t.repo ["fetch", "-q", "origin"]

/-- Any executable in t.fakebin; its path. -/
def fake (t : T) (name body : String) : IO String := do
  let fb := (← t.fakebin).getD (t.d ++ "/fb")
  t.fakebinR.set (some fb)
  IO.FS.createDirAll fb
  put (fb ++ "/" ++ name) body "755"
  return fb ++ "/" ++ name

/-- Fake hc, gh and launch script: hc ls answers from setHc (absent: hc fails); gh answers from setGh by subcommand
(absent: fails); the launch script logs its argv and the task rows it saw. Every call is logged to <name>.log. -/
def fakes (t : T) : IO Unit := do
  let D := shquote t.d
  discard <| t.fake "hc" s!"#!/bin/sh\necho \"$*\" >> {D}/hc.log\nif [ \"$1\" = ls ]; then\n  [ -f {D}/hc.json ] || exit 1\n  cat {D}/hc.json; echo\nelse echo '\{}'; fi\n"
  discard <| t.fake "gh" s!"#!/bin/sh\necho \"$*\" >> {D}/gh.log\n[ -f {D}/gh.\"$1\" ] || exit 1\ncat {D}/gh.\"$1\"\n"
  let l := t.d ++ "/launch"
  t.launchR.set (some l)
  put l s!"#!/bin/sh\nexec {shquote (← selfBin)} --fake-launch {D} \"$@\"\n" "755"

/-- The launch fake's body: logs argv to launch.log and {argv, task} to launch.calls; fails when launch.fail exists. -/
def fakeLaunch (d : String) (argv : List String) : IO UInt32 := do
  let h ← IO.FS.Handle.mk (d ++ "/launch.log") .append
  h.putStrLn (" ".intercalate argv)
  let c ← Sqlite.Conn.open ((← IO.getEnv "SWARM_DB").getD "") false
  let rows ← c.query "select owner,state from task"
  let task := rows.map fun r => Json.arr (r.map cell)
  let h ← IO.FS.Handle.mk (d ++ "/launch.calls") .append
  h.putStrLn (Json.mkObj [("argv", toJson argv), ("task", Json.arr task)]).compress
  if ← (d ++ "/launch.fail" : System.FilePath).pathExists then
    IO.eprint "no Herdr window\nmore\n"
    return 1
  IO.println "hc1"
  return 0

/-- hc ls --json lists these terminals (objects, state live unless given); none: hc ls fails. -/
def setHc (t : T) (ts : List Json) : IO Unit := do
  let f := t.d ++ "/hc.json"
  if ts.isEmpty then
    try IO.FS.removeFile f catch _ => pure ()
    return
  let ts := ts.map fun x => if x.f "state" == .null then x.setObjVal! "state" "live" else x
  put f (Json.mkObj [("terminals", toJson ts)]).compress

/-- gh <sub> prints `out`; none: it fails (rate limited). -/
def setGh (t : T) (sub : String) (out : Option String) : IO Unit := do
  let f := t.d ++ "/gh." ++ sub
  match out with
  | none => try IO.FS.removeFile f catch _ => pure ()
  | some s => put f s

/-- gh <sub> prints this JSON. -/
def setGhJ (t : T) (sub : String) (out : Json) : IO Unit := t.setGh sub (some out.compress)

/-- The argv lines a fake logged. -/
def calls (t : T) (name : String) : IO (List String) := do
  return match ← slurp s!"{t.d}/{name}.log" with | some s => splitlines s | none => []

/-- One {argv, task} per launch. -/
def launched (t : T) : IO (Array Json) := do
  let s := (← slurp (t.d ++ "/launch.calls")).getD ""
  return (splitlines s).toArray.map fun l => (Json.parse l).toOption.getD .null

/-- An hc whose ls shows these terminals live. -/
def liveHc (t : T) (addrs : List String) : IO Unit := do
  let ts := addrs.map fun a => Json.mkObj [("address", Json.str a), ("state", "live")]
  discard <| t.fake "hc" s!"#!/bin/sh\n[ \"$1\" = ls ] && echo '{(Json.mkObj [("terminals", toJson ts)]).compress}' || echo '\{}'\n"

/-- A fresh fixture. -/
def new : IO T := do
  let tmp := (← IO.getEnv "TMPDIR").getD "/tmp"
  let r ← IO.Process.output { cmd := "mktemp", args := #["-d", s!"{tmp}/swarm-cli-XXXXXX"] }
  if r.exitCode ≠ 0 then fail s!"mktemp: {r.stderr}"
  -- realpath: git and lsof report /private/var, not /var
  let d := (← IO.FS.realPath (strip r.stdout)).toString
  -- the cmd-cost history is per user: never the real one
  IO.FS.createDirAll (d ++ "/.state")
  Shim.setenv "XDG_STATE_HOME" (d ++ "/.state")
  let t : T := { d, repo := d ++ "/repo", wt := d ++ "/wt", db := d ++ "/swarm.db",
                 cwds := ← IO.mkRef [("a", d ++ "/repo"), ("b", d ++ "/wt")], fakebinR := ← IO.mkRef none,
                 launchR := ← IO.mkRef none, cleanups := ← IO.mkRef #[] }
  IO.FS.createDir t.repo
  discard <| t.git t.repo ["init", "-q", "-b", "main"]
  put (t.repo ++ "/a.txt") "x"; put (t.repo ++ "/b.txt") "x"; put (t.repo ++ "/e.txt") "mod (p, q)\n"
  discard <| t.git t.repo ["add", "."]
  discard <| t.git t.repo ["commit", "-qm", "init"]
  discard <| t.git t.repo ["worktree", "add", "-q", "-b", "w2", t.wt]
  return t

/-- Runs the deferred actions (last first); removes the dir when the test passed. -/
def cleanup (t : T) (passed : Bool) : IO Unit := do
  for act in (← t.cleanups.get).reverse do try act catch _ => pure ()
  if passed then discard <| IO.Process.output { cmd := "rm", args := #["-rf", t.d] }

end T
end SwarmLean.Tests.Cli

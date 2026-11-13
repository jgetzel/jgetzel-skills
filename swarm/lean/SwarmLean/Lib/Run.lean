import SwarmLean.Sys
import SwarmLean.Lib.Json
import SwarmLean.Lib.Machine
import SwarmLean.Lib.Re
import SwarmLean.Db

/-! run.lua's helpers: hc machines, live jobs, the remote probe and its readings (watchd's remote_tick), a landed
worktree's remote dirs (clean_remote), the job's environment. `swarm run` itself is Cmd/Run.lean. -/

namespace SwarmLean.Run
open Lean (Json)

variable {m : Type → Type} [Monad m]

/-- Under each machine's home: `<repo>/<worktree>/{src,jobs/<id>}`. -/
def RUN_DIR : String := ".cache/swarm-run"
/-- Lines of the job's log printed at its end. -/
def JOB_TAIL : Nat := 200
/-- A job whose terminal is gone this long gets a job-end 'lost'. -/
def LOST_FOR : Int := 3600

/-- An object of the fields that are set: a Lua table's nil fields are absent from cjson's output. -/
def obj (l : List (String × Option Json)) : Json := Json.mkObj (l.filterMap fun (k, v) => v.map (k, ·))

/-- `{name: machine}` from `hc machine ls --json`, [] without hc (run.hc_machines). -/
def hcMachines [Proc m] : m (List (String × Json)) := do
  let txt := match ← Proc.output ["hc", "machine", "ls", "--json"] none [] with
    | some o => if o.code == 0 then o.stdout else "{}"
    | none => "{}"
  let ms := ((Json.decode txt).bind (Json.field · "machines")).map Json.items |>.getD []
  return (ms.filterMap fun x => (Json.fstr x "name").map (·, x)).reverse

/-- A job-start event with no job-end: its record, start, agent and id (the event's path). -/
structure Job where
  ts : Int
  agent : Option String
  id : Option String
  data : Json

/-- A string field of the job's record. -/
def Job.s (j : Job) (k : String) : Option String := Json.fstr j.data k

/-- job-start events with no job-end yet, newest first, from the last day (run.live_jobs). -/
def liveJobs (db : Db) (t : Int) : List Job :=
  let ended := (db.events.filter (·.kind == some "job-end")).map (·.path)
  ((db.events.filter fun e => e.kind == some "job-start" && e.ts.getD 0 > t - 86400 && e.ts.isSome).reverse).filterMap fun e =>
    if ended.contains e.path then none else
    match Json.decode (e.data.getD "{}") with
    | some j@(.obj _) => some { ts := e.ts.getD 0, agent := e.agent, id := e.path, data := j }
    | _ => none

/-- The probe: load and memory, then with job terminals as args every process and each terminal's `hc get`. -/
def PROBE : String := "if [ \"$(uname)\" = Darwin ]; then echo @darwin; for k in hw.ncpu hw.memsize kern.memorystatus_vm_pressure_level " ++
  "vm.loadavg; do sysctl -n $k 2>/dev/null || echo; done; vm_stat; " ++
  "else nproc; cat /proc/loadavg /proc/meminfo; cat /proc/pressure/memory 2>/dev/null; fi; [ $# -gt 0 ] || exit 0; " ++
  "echo @ps; LC_ALL=C ps -Ao pid=,ppid=,rss=,pcpu=; " ++
  "for t; do echo \"@hc $t\"; hc get \"$t\" --json 2>&1 | tr -d '\\n'; echo; done"

/-- Lua's `s:match(pat .. "%s+(%d+)")`: the digits after the first `pat` followed by spaces. -/
def numAfterSp (s pat : String) : Option Int :=
  (s.splitOn pat).tail.findSome? fun r =>
    let sp := r.toList.takeWhile isSpace
    let ds := (r.toList.drop sp.length).takeWhile Char.isDigit
    if sp.isEmpty || ds.isEmpty then none else parseInt (String.ofList ds)

/-- A machine's reading from the probe's head. -/
structure Probe where
  cores : Int
  load : Float
  avail_kb : Int
  total_kb : Int
  psi : Option Float := none
  level : Option String := none
  deriving BEq, Repr

/-- The probe's head (before `@ps`) as a reading, none when unreadable (run.parse_probe). -/
def parseProbe (head : String) : Option Probe :=
  let l := splitlines head
  if l.head? == some "@darwin" then do
    let (avail, total, p) ← Machine.darwinMem (l.getD 2 "") (some ("\n".intercalate (l.drop 5))) (l.getD 3 "") (l.getD 4 "") (l.getD 1 "")
    let cores ← p.cores
    let load ← p.load
    pure { cores, load, avail_kb := avail, total_kb := total, level := some (p.level.getD "unknown") }
  else do
    let cores ← parseInt (l.getD 0 "")
    let load ← parseFloat ((words (l.getD 1 "")).headD "")
    let avail ← numAfterSp head "MemAvailable:"
    let total ← numAfterSp head "MemTotal:"
    pure { cores, load, avail_kb := avail, total_kb := total,
           psi := some (((Machine.numAfter head "some avg10=" true).bind parseFloat).getD 0) }

/-- A reading as JSON (meta 'machines'), with what watchd adds. -/
def Probe.json (p : Probe) (extra : List (String × Option Json)) : Json :=
  obj ([("cores", some (Json.int p.cores)), ("load", some (Json.float p.load)), ("avail_kb", some (Json.int p.avail_kb)),
    ("total_kb", some (Json.int p.total_kb)), ("psi", p.psi.map Json.float), ("level", p.level.map .str)] ++ extra)

/-- `ps -Ao pid=,ppid=,rss=,pcpu=` lines: (pid, ppid, rss KiB, %cpu). -/
def psLine (l : String) : Option (Nat × Nat × Int × Float) :=
  match words l with
  | a :: b :: c :: e :: _ =>
    if !(l.toList.dropWhile isSpace).head?.any Char.isDigit then none else
    let cpu := String.ofList (e.toList.takeWhile fun ch => ch.isDigit || ch == '.')
    match a.toNat?, b.toNat?, c.toNat?, parseFloat cpu with
    | some p, some q, some r, some f => if cpu.isEmpty then none else some (p, q, r, f)
    | _, _, _, _ => none
  | _ => none

/-- RSS (KiB) and %CPU summed over root and its descendants. shortcut: %CPU is ps's (lifetime average on Linux). -/
def treeSum (ps : List (Nat × Nat × Int × Float)) (root : Nat) : Int × Float := Id.run do
  let mut q := [root]
  let mut seen : List Nat := []
  let mut rss : Int := 0
  let mut cpu : Float := 0
  for _ in [0:ps.length + 1] do
    match q with
    | [] => break
    | p :: rest =>
      q := rest
      if seen.contains p then continue
      seen := p :: seen
      if let some (_, _, r, c) := ps.find? (·.1 == p) then rss := rss + r; cpu := cpu + c
      q := q ++ ((ps.filter fun x => x.2.1 == p && x.1 != p).map (·.1))
  return (rss, cpu)

/-- What the probe said after `@ps`: the processes and each terminal's `hc get` line. -/
def parsePs (txt : String) : List (Nat × Nat × Int × Float) × List (String × String) := Id.run do
  let tail := match txt.splitOn "\n@ps\n" with | _ :: rest@(_ :: _) => "\n@ps\n".intercalate rest | _ => ""
  let mut ps := []
  let mut got : List (String × String) := []
  let mut cur : Option String := none
  for l in splitlines tail do
    if l.startsWith "@hc " && !(l.drop 4).toString.isEmpty && !((l.drop 4).toString.toList.any isSpace) then
      cur := some (l.drop 4).toString
      got := (cur.get!, "") :: got.filter (·.1 != cur.get!)
    else if let some c := cur then got := (c, l) :: got.filter (·.1 != c)
    else if let some p := psLine l then ps := ps ++ [p]
  return (ps, got)

/-- `{rss_kb, cpu}` per live job, `{gone = since}` where the machine says its terminal is gone or ended; the jobs lost
an hour (their `swarm run` gone too) for watchd to end (run.job_readings). -/
def jobReadings [Sys m] (t : Int) (txt : String) (mine : List (Job × String)) (old : Json) : m (List (String × Json) × List Job) := do
  let (ps, got) := parsePs txt
  let mut out := []
  let mut lost := []
  for (j, term) in mine do
    let g := match Json.decode ((got.lookup term).getD "") with | some g@(.obj _) => g | _ => Json.mkObj []
    let pid := (Json.field g "pid").bind fun p => match p with | .str s => parseInt s | x => Json.int? x
    let jid := j.id.getD ""
    if Json.fstr g "state" == some "live" && pid.isSome then
      let (rss, cpu) := treeSum ps pid.get!.toNat
      out := out ++ [(jid, obj [("rss_kb", some (Json.int rss)), ("cpu", some (Json.int (cpu + 0.5).floor.toInt64.toInt))])]
    else if (Json.field g "state").isSome || ((Json.field g "error").bind (Json.fstr · "kind")) == some "not_found" then
      let since := ((Json.field old jid).bind (Json.fint · "gone")).getD t
      out := out ++ [(jid, obj [("gone", some (Json.int since))])]
      let alive ← match (Json.field j.data "pid").bind Json.int? with
        | some p => Sys.pidAlive p
        | none => pure false
      if t - since ≥ LOST_FOR && !alive then lost := lost ++ [j]
  return (out, lost)

/-- watchd's probe of each hc machine (run.remote_tick): load, memory and its jobs' trees in meta 'machines'; the jobs
lost an hour get a job-end. Only a watchd started from a Herdr terminal probes. -/
def remoteTick [Env m] [Proc m] [Sys m] [Store m] [Clock m] (t : Int) : m Unit := do
  if (← env "HC_TERMINAL_ID").isNone then return
  let ms ← hcMachines
  let db ← Store.txn [.«meta», .event] fun db => (db, db)
  let old := ((db.getMeta "machines").bind (·.v) |>.bind Json.decode).getD (Json.mkObj [])
  let jobs := liveJobs db t
  let names := (ms.map (·.1)).eraseDups.mergeSort (· ≤ ·)
  let mut out : List (String × Json) := []
  let mut lost : List Job := []
  for n in names do
    let mc := (ms.lookup n).getD (Json.mkObj [])
    let o := match Json.field old n with | some x@(.obj _) => x | _ => Json.mkObj []
    let mine := jobs.filterMap fun j => if j.s "machine" == some n then (j.s "hc").map fun hc =>
      (j, match hc.splitOn "/" with | _ :: rest@(_ :: _) => if "/".intercalate rest == "" then hc else "/".intercalate rest | _ => hc) else none
    let st := Json.fstr mc "state"
    let txt ← if st == some "connected" then
        (do match ← Proc.output (["hc", "exec", "--on", n, "--timeout", "10", "sh", "-c", PROBE, "sh"] ++ mine.map (·.2)) none [] with
          | some r => pure (if r.code == 0 then some r.stdout else none)
          | none => pure none)
      else pure none
    let head := txt.map fun x => match x.splitOn "\n@ps\n" with | h :: _ :: _ => h | _ => x
    match head.bind parseProbe with
    | some p =>
      let oldJobs := match Json.field o "jobs" with | some x@(.obj _) => x | _ => Json.mkObj []
      let (rd, l) ← jobReadings t txt.get! mine oldJobs
      lost := lost ++ l
      out := out ++ [(n, p.json [("state", some (.str "connected")), ("ts", some (Json.int t)), ("jobs", some (Json.mkObj rd))])]
    | none =>
      let s := if st != some "connected" then st.getD "nil" else "unreachable"
      let since := if Json.fstr o "state" == some s then (Json.fint o "since").getD t else t
      out := out ++ [(n, obj [("state", some (.str s)), ("ts", some (Json.int t)), ("since", some (Json.int since))])]
  let now ← Clock.now
  Store.txn [.«meta»] fun db =>
    let db := lost.foldl (fun db j => db.log now j.agent "job-end" j.id (some (Json.encode (obj [("machine", (j.s "machine").map .str),
      ("exit", some (.str "lost")), ("s", some (Json.int (t - j.ts)))])))) db
    (db.setMeta "machines" (some (Json.encode (Json.mkObj out))), ())

/-- A job's copy, `RUN_DIR/<repo>/<worktree>`, with no `..` that would climb out of it. -/
def runDirOk (dir : String) : Bool :=
  (Re.fullmatch (Re.escape RUN_DIR ++ "/[\\w.-]+/[\\w.-]+") dir).toOption.join.isSome && !(dir.splitOn "/").contains ".."

/-- Removes a landed worktree's dirs on every machine its jobs ran on (run.clean_remote). -/
def cleanRemote [Proc m] [Store m] [Clock m] (wt : String) : m Unit := do
  let db ← Store.txn [.event] fun db => (db, db)
  let mut seen : List (String × String) := []
  for e in db.events.filter (·.kind == some "job-start") do
    let some j := Json.decode (e.data.getD "{}") | continue
    let some mach := Json.fstr j "machine" | continue
    let some dir := Json.fstr j "dir" | continue
    if mach == "" || Json.fstr j "wt" != some wt || seen.contains (mach, dir) then continue
    unless runDirOk dir do continue
    seen := (mach, dir) :: seen
    let ok := (← Proc.output ["hc", "exec", "--on", mach, "--timeout", "120", "rm", "-rf", dir] none []).any (·.code == 0)
    let now ← Clock.now
    Store.txn [] fun db => (db.log now none "remote-clean" (some dir) (some s!"{mach} {if ok then "ok" else "failed"}"), ())

/-- ssh with one shared connection per host that gives up fast on a sleeping host (run.ssh_cmd). -/
def sshCmd [Env m] : m (List String) := do
  let cp := ((← Env.var "TMPDIR").getD "/tmp") ++ "/swarm-ssh-%C"
  return ["ssh", "-o", "BatchMode=yes", "-o", "ConnectTimeout=5", "-o", "ServerAliveInterval=5", "-o",
    "ServerAliveCountMax=3", "-o", "ControlMaster=auto", "-o", s!"ControlPath={cp}", "-o", "ControlPersist=120"]

/-- Names (no value) `env_scan`'s [glob, regex] pairs find in files under top. -/
def scanNames [Sys m] [Fs m] [Env m] [MonadExceptOf Exit m] (cfg : Json) (top : String) : m (List String) := do
  let mut names := []
  for ps in Json.items ((Json.field cfg "env_scan").getD .null) do
    let glob := ((Json.items ps).head?.bind Json.str?).getD ""
    let rx := ((Json.items ps)[1]?.bind Json.str?).getD ""
    let r ← Sys.exec ["sh", "-c", "IFS=; for f in $1; do [ -f \"$f\" ] && printf \"%s\\0\" \"$f\"; done", "sh", glob] { cwd := some top }
    for f in r.stdout.splitOn "\x00" do
      if f == "" then continue
      if let some s ← Fs.read (joinPath top f) then
        names := names ++ (← orDie (Re.findall rx s)).map (·.headD "")
  return names

/-- The variables the job gets: names matching a `run.env` regex, names `run.env_scan` finds, and --env (run.job_env). -/
def jobEnv [Sys m] [Fs m] [Env m] [MonadExceptOf Exit m] (cfg : Json) (top : String) (extra : List String) : m (List (String × String)) := do
  let names ← scanNames cfg top
  let pats := (Json.items ((Json.field cfg "env").getD .null)).filterMap Json.str?
  let all ← Sys.environ
  let mut env := []
  for (k, v) in all do
    let mut hit := names.contains k
    for p in pats do
      hit := hit || (← orDie (Re.search p k)).isSome
    if hit then env := env ++ [(k, v)]
  for e in extra do
    match e.splitOn "=" with
    | k :: v@(_ :: _) => env := (k, "=".intercalate v) :: env.filter (·.1 != k)
    | _ => if let some v := all.lookup e then env := (e, v) :: env.filter (·.1 != e)
  return env

end SwarmLean.Run

import SwarmLean.World
import SwarmLean.Sys
import SwarmLean.Db
import Std.Data.HashMap
import Lean.Data.Json

/-! machine.lua: this machine's processes and memory, memory per owner, background jobs, other machines from watchd's
cache, and the machine note. -/

namespace SwarmLean.Machine

variable {m : Type → Type}

/-- A pressure reading: Linux PSI some avg10 (`memory`, `cpu`), or macOS `level`, `load` and `cores`. -/
structure Psi where
  memory : Option Float := none
  cpu : Option Float := none
  level : Option String := none
  load : Option Float := none
  cores : Option Int := none

/-- The /proc root (machine.PROC): $SWARM_PROC as set, else /proc. -/
def procRoot [Monad m] [Env m] : m String := return (← Env.var "SWARM_PROC").getD "/proc"

/-- The system (machine.OS): $SWARM_OS as set, else this build's. -/
def osName [Monad m] [Env m] : m String :=
  return (← Env.var "SWARM_OS").getD (if System.Platform.isOSX then "Darwin" else "Linux")

/-- Lua's `s:match(pat .. "(%d+)")`: the digits after the first `pat` in `s`. -/
def numAfter (s pat : String) (frac : Bool := false) : Option String :=
  match s.splitOn pat with
  | _ :: rest :: _ =>
    let ds := rest.toList.takeWhile fun c => c.isDigit || (frac && c == '.')
    if ds.isEmpty then none else some (String.ofList ds)
  | _ => none

/-- macOS readings to (avail KiB, total KiB, pressure) (machine.darwin_mem). -/
def darwinMem (memsize : String) (vmstat : Option String) (level loadavg ncpu : String) : Option (Int × Int × Psi) := do
  let total ← parseInt memsize
  let vm ← vmstat
  let pg := ((numAfter vm "page size of ").bind parseInt).getD 4096
  let count (k : String) : Int := match (vm.splitOn s!"Pages {k}:")[1]? with
    | some r => (parseInt (String.ofList ((r.toList.dropWhile isSpace).takeWhile Char.isDigit))).getD 0
    | none => 0
  let pages := count "free" + count "inactive" + count "speculative" + count "purgeable"
  let lvl := match parseInt level with
    | some 1 => some "normal" | some 2 => some "warn" | some 4 => some "critical" | _ => none
  let load := (String.ofList ((loadavg.toList.dropWhile fun c => !(c.isDigit || c == '.')).takeWhile fun c => c.isDigit || c == '.'))
  pure (fdiv (pages * pg) 1024, fdiv total 1024, { level := lvl, load := parseFloat load, cores := parseInt ncpu })

/-- Memory available and total in KiB and the pressure, none when unreadable (machine.mem). -/
def mem [Monad m] [Env m] [Fs m] [Proc m] : m (Option (Int × Int × Psi)) := do
  if (← osName) == "Darwin" then
    let sc (k : String) : m String := do
      return strip ((← Proc.output ["sysctl", "-n", k] none []).map (·.stdout) |>.getD "")
    let vm := (← Proc.output ["vm_stat"] none []).map (·.stdout)
    return darwinMem (← sc "hw.memsize") vm (← sc "kern.memorystatus_vm_pressure_level") (← sc "vm.loadavg") (← sc "hw.ncpu")
  let root ← procRoot
  let some s ← Fs.read (root ++ "/meminfo") | return none
  let field (k : String) : Option Int := (s.splitOn "\n").findSome? fun l =>
    match l.splitOn ":" with
    | key :: rest@(_ :: _) =>
      if key == k then parseInt (String.ofList ((":".intercalate rest).toList.dropWhile isSpace |>.takeWhile Char.isDigit)) else none
    | _ => none
  let psi (r : String) : m Float := do
    return (((← Fs.read s!"{root}/pressure/{r}").bind fun t => numAfter t "some avg10=" true).bind parseFloat).getD 0
  match field "MemAvailable", field "MemTotal" with
  | some a, some t => return some (a, t, { memory := some (← psi "memory"), cpu := some (← psi "cpu") })
  | _, _ => return none

/-- Memory or CPU pressure is high (machine.pressure_high). -/
def pressureHigh (avail total : Int) (psi : Psi) : Bool :=
  match psi.level with
  | some l => l != "normal"
  | none => psi.memory.getD 0 > 10 || Float.ofInt avail < 0.15 * Float.ofInt total

/-- The one machine line (machine.machine_line). -/
def line (avail total : Int) (psi : Psi) : String :=
  let memS := s!"machine: {fixed (Float.ofInt avail / 1048576) 1}/{fixed (Float.ofInt total / 1048576) 1}G mem available, "
  match psi.memory with
  | none =>
    memS ++ s!"pressure {psi.level.getD "unknown"}, load {(psi.load.map fmtG).getD "?"} on {(psi.cores.map toString).getD "?"} cores"
  | some mm => memS ++ s!"pressure10 mem {fmtG mm}% cpu {fmtG (psi.cpu.getD 0)}%"

/-- The machine line, or that memory is unreadable (machine.machine_line with nil). -/
def lineOf : Option (Int × Int × Psi) → String
  | some (a, t, p) => line a t p
  | none => "machine: unknown (memory unreadable)"

/-- `ps` time (`[[dd-]hh:]mm:ss[.cc]`, both systems' etime and time) in seconds (machine.ps_secs). -/
def psSecs (s : String) : Int :=
  let ds := s.toList.takeWhile Char.isDigit
  let (dd, rest) := if !ds.isEmpty && (s.toList.drop ds.length).head? == some '-' then
      ((String.ofList ds).toNat?.getD 0, String.ofList (s.toList.drop (ds.length + 1))) else (0, s)
  let n := ((rest.splitOn ":").filter (· ≠ "")).foldl (fun n x => n * 60 + (parseFloat x).getD 0) 0.0
  (Float.floor (n + Float.ofNat (dd * 86400))).toInt64.toInt

/-- One process as `ps` lists it (a row of machine.parse_ps). -/
structure Ps where
  pid : Int
  ppid : Int
  rss_kb : Int
  age : Int
  cpu_s : Int
  args : String
  argv : List String
  comm : String
  deriving Repr, BEq, Inhabited

/-- One line of `ps -o pid=,ppid=,rss=,etime=,time=,args=`, none when it is not one. -/
def parsePsLine (l : String) : Option Ps := do
  let num (cs : List Char) : Option (Int × List Char) :=
    let ds := cs.takeWhile Char.isDigit
    if ds.isEmpty then none else some ((String.ofList ds).toNat?.getD 0, cs.drop ds.length)
  let sp (cs : List Char) : Option (List Char) := if cs.head?.any isSpace then some (cs.dropWhile isSpace) else none
  let tok (cs : List Char) : Option (String × List Char) :=
    let t := cs.takeWhile (!isSpace ·)
    if t.isEmpty then none else some (String.ofList t, cs.drop t.length)
  let (pid, cs) ← num (l.toList.dropWhile isSpace)
  let (ppid, cs) ← num (← sp cs)
  let (rss, cs) ← num (← sp cs)
  let (et, cs) ← tok (← sp cs)
  let (tm, cs) ← tok (← sp cs)
  let args := String.ofList (if cs.head?.any isSpace then cs.tail else cs)
  let argv := words args
  pure { pid, ppid, rss_kb := rss, age := psSecs et, cpu_s := psSecs tm, args, argv, comm := basename (argv.headD "") }

/-- `ps` text as its processes, in its order; a pid listed twice keeps its last line (machine.parse_ps). -/
def parsePs (txt : String) : List Ps :=
  let ps := ((txt.splitOn "\n").filter (· ≠ "")).filterMap parsePsLine
  ps.filter fun p => !(ps.dropWhile (· != p)).tail.any (·.pid == p.pid)

/-- Every process, one `ps` (machine.procs). -/
def procs [Monad m] [Proc m] : m (List Ps) := do
  let o ← Proc.output ["ps", "-axww", "-o", "pid=,ppid=,rss=,etime=,time=,args="] none [("LC_ALL", "C")]
  return parsePs (match o with | some o => if o.code == 0 then o.stdout else "" | none => "")

/-- The processes by pid. -/
def byPid (ps : List Ps) : Std.HashMap Int Ps := ps.foldl (fun h p => h.insert p.pid p) {}

/-- `lsof -Fpn` text as each pid's path, a pid's last `n` line winning (machine.parse_lsof). -/
def parseLsof (txt : String) : List (Int × String) :=
  let step (acc : List (Int × String) × Option Int) (l : String) :=
    let (out, pid) := acc
    let v := (l.drop 1).toString
    if l.startsWith "p" then (out, parseInt v)
    else if l.startsWith "n" then match pid with
      | some p => (out.filter (·.1 != p) ++ [(p, v)], pid)
      | none => acc
    else acc
  (((txt.splitOn "\n").filter (· ≠ "")).foldl step ([], none)).1

/-- The cgroup root (machine.CGROUP): $SWARM_CGROUP as set, else /sys/fs/cgroup. -/
def cgroupRoot [Monad m] [Env m] : m String := return (← Env.var "SWARM_CGROUP").getD "/sys/fs/cgroup"

/-- The scope path in a cgroup line's rest, as Lua's greedy `(/[^\n]*/swarm%-agent%-[^/\n]*%.scope)`. -/
def scopeAt (l : List Char) : Option String :=
  if l.head? != some '/' then none else
  let pre := "/swarm-agent-".toList
  let js := (List.range l.length).reverse.filter fun j => j ≥ 1 && (l.drop j).take pre.length == pre
  js.findSome? fun j =>
    let run := (l.drop (j + pre.length)).takeWhile (· ≠ '/')
    let ks := (List.range (run.length + 1)).reverse.filter fun k => k ≥ 6 && (run.take k).drop (k - 6) == ".scope".toList
    ks.head?.map fun k => String.ofList (l.take (j + pre.length + k))

/-- Lua's `s:match("0::(/[^\n]*/swarm%-agent%-[^/\n]*%.scope)")`. -/
def scopeOf (s : String) : Option String :=
  let rec go : List Char → Option String
    | [] => none
    | l@(_ :: rest) =>
      if l.take 3 == ['0', ':', ':'] then
        match scopeAt ((l.drop 3).takeWhile (· ≠ '\n')) with
        | some r => some r
        | none => go rest
      else go rest
  go s.toList

/-- A swarm-agent scope's directory, peak memory (KiB) and CPU seconds. -/
structure Cgroup where
  dir : String
  peak_kb : Int
  cpu_s : Int
  deriving Repr, BEq

/-- The cgroup of the swarm-agent scope `pid` runs in, none where there is none (machine.cgroup). -/
def cgroup [Monad m] [Env m] [Fs m] (pid : Int) : m (Option Cgroup) := do
  let some rel := scopeOf ((← Fs.read s!"{← procRoot}/{d pid}/cgroup").getD "") | return none
  let dir := (← cgroupRoot) ++ rel
  let some peak := (← Fs.read s!"{dir}/memory.peak").bind parseInt | return none
  let usec := (((← Fs.read s!"{dir}/cpu.stat").getD "") |> (numAfter · "usage_usec ")).bind parseInt |>.getD 0
  return some { dir, peak_kb := fdiv peak 1024, cpu_s := fdiv usec 1000000 }

/-- argv as `tool arg …` with path and interpreter stripped, so `node /x/tsc` reads as `tsc` (machine.proc_cmd). -/
def procCmd (p : Ps) : String :=
  let w := p.argv.mapIdx fun i x => if i < 2 then basename x else x
  let interp (x : String) : Bool := x == "node" || x == "bash" || x == "sh" ||
    (x.startsWith "python" && ((x.drop 6).toString.all fun c => c.isDigit || c == '.'))
  " ".intercalate (if w.length > 1 && interp (w.headD "") then w.tail else w)

/-- Memory held by one owner: an agent, or "other session" (a row of machine.holders). -/
structure Holder where
  agent : String
  kb : Int := 0
  top : Option String := none
  top_kb : Int := -1
  age : Option Int := none
  /-- the tree's processes, its claude excluded -/
  procs : List Ps := []
  deriving Repr, BEq, Inhabited

/-- Each live agent's claude process: pid and name. -/
def claudeOwners (agents : List Agent) : List (Int × String) :=
  (agents.filter (·.ended.isNone)).filterMap fun a => a.claude_pid.map (·, a.name)

/-- Whose claude process `q` is under, looking up at most `n` processes. -/
def walkOwner (owner : List (Int × String)) (by_ : Std.HashMap Int Ps) : Nat → Ps → Option String
  | 0, _ => none
  | n + 1, q => match owner.lookup q.pid with
    | some w => some w
    | none => if hasSub q.comm "claude" then some "other session" else
      match by_.get? q.ppid with
      | some q' => walkOwner owner by_ n q'
      | none => none

/-- Memory held per owner, by measurement, biggest first (machine.holders). -/
def holders (agents : List Agent) (ps : List Ps) : List Holder :=
  let owner := claudeOwners agents
  let by_ := byPid ps
  let hs := ps.foldl (init := ([] : List Holder)) fun hs p =>
    match walkOwner owner by_ 64 p with
    | none => hs
    | some who =>
      let h := (hs.find? (·.agent == who)).getD { agent := who }
      let own := (owner.lookup p.pid).isSome
      let h := { h with kb := h.kb + p.rss_kb, procs := if own then h.procs else h.procs ++ [p] }
      let h := if p.rss_kb > h.top_kb && !own then { h with top := some (procCmd p), top_kb := p.rss_kb, age := some p.age } else h
      if hs.any (·.agent == who) then hs.map fun x => if x.agent == who then h else x else hs ++ [h]
  hs.mergeSort fun a b => a.kb > b.kb || (a.kb == b.kb && a.agent ≤ b.agent)

/-- The agents running a Bash-tool shell under their claude process, each with that process (machine.bg_agents). -/
def bgAgents (agents : List Agent) (ps : List Ps) : List (String × Ps) :=
  let owner := claudeOwners agents
  ps.foldl (init := []) fun out p => match owner.lookup p.ppid with
    | some n => if hasSub p.args "/shell-snapshots/snapshot-" then out.filter (·.1 != n) ++ [(n, p)] else out
    | none => out

/-- The text after the first `pre` up to the last `post` after it (Lua's `match(pre .. "(.*)" .. post)`). -/
def between (s pre post : String) : Option String :=
  match s.splitOn pre with
  | _ :: rest@(_ :: _) =>
    let r := pre.intercalate rest
    match r.splitOn post with
    | q@(_ :: _ :: _) => some (post.intercalate q.dropLast)
    | _ => none
  | _ => none

/-- The user's command of a Bash-tool job process: inside `eval '…'`, else the last 200 characters (machine.job_cmd). -/
def jobCmd (args : String) : String :=
  match (between args "eval '" "' < /dev/null").orElse fun _ => between args "eval '" "'" with
  | some inner => inner.replace "'\\''" "'"
  -- shortcut: the last 200 characters, where Lua takes bytes; differs only on non-ASCII command lines
  | none => if args.length > 200 then String.ofList (args.toList.drop (args.length - 200)) else args

/-- A job-start event with no job-end yet: its time, agent, id and data (a row of machine.live_jobs). -/
structure Job where
  ts : Option Int
  agent : Option String
  id : Option String
  data : Lean.Json

/-- A text field of a job's data. -/
def Job.str (j : Job) (k : String) : Option String := (j.data.getObjValAs? String k).toOption

/-- job-start events of the last day with no job-end, newest first (machine.live_jobs). -/
def liveJobs (events : List Event) (t : Int) : List Job :=
  let ended := (events.filter (·.kind == some "job-end")).map (·.path)
  (events.filter fun e => e.kind == some "job-start" && e.ts.getD 0 > t - 86400).reverse.filterMap fun e =>
    if ended.contains e.path then none else
    match Lean.Json.parse (e.data.getD "{}") with
    | .ok j@(.obj _) => some { ts := e.ts, agent := e.agent, id := e.path, data := j }
    | _ => none

/-- A JSON field as a number. -/
def jnum (j : Lean.Json) (k : String) : Option Float :=
  match j.getObjVal? k with
  | .ok (.num n) => some n.toFloat
  | _ => none

/-- A JSON field as text. -/
def jstr (j : Lean.Json) (k : String) : Option String := (j.getObjValAs? String k).toOption

/-- One line per other machine from watchd's cache, with this repo's live jobs on it (machine.remote_lines). -/
def remoteLines [Monad m] [Clock m] (metas : List Meta) (events : List Event) (t : Int) : m (List String) := do
  let some r := metas.find? (·.k == "machines") | return []
  let .ok (.obj kv) := Lean.Json.parse (r.v.getD "") | return []
  let jobs := liveJobs events t
  let now ← Clock.now
  let names := (kv.toList.map (·.1)).mergeSort (· ≤ ·)
  let mut out := []
  for n in names do
    let mj := (kv.toList.lookup n).getD .null
    let num (k : String) : Int := ((jnum mj k).map (·.floor.toInt64.toInt)).getD 0
    let js := (jobs.filter (·.str "machine" == some n)).map fun j =>
      let rd := match mj.getObjVal? "jobs" with
        | .ok jm@(.obj _) => (j.id.map fun i => (jm.getObjVal? i).toOption).join
        | _ => none
      s!"{j.agent.getD "nil"} {cut ((j.str "cmd").getD "") 24} {ago now (j.ts.getD 0)}" ++
        (match rd.bind (jnum · "rss_kb") with | some k => s!" {fixed (k / 1048576) 1}G" | none => "")
    if jstr mj "state" != some "connected" then
      let since := match jnum mj "since" with | some s => s | none => (jnum mj "ts").getD 0
      out := out ++ [s!"{n}: {(jstr mj "state").getD "nil"} since {← Clock.hhmm since.floor.toInt64.toInt}"]
    else
      let old := if t - num "ts" > 120 then s!" (as of {ago now (num "ts")} ago)" else ""
      let lvl := (jstr mj "level").getD s!"{fmtG ((jnum mj "psi").getD 0)}%"
      out := out ++ [s!"{n}: {fixed ((jnum mj "avail_kb").getD 0 / 1048576) 0}/{fixed ((jnum mj "total_kb").getD 0 / 1048576) 0}G available, load {fmtG ((jnum mj "load").getD 0)} on {num "cores"} cores, mem pressure {lvl}{old}{if js.isEmpty then "" else ", jobs: " ++ ", ".intercalate js}"]
  return out

/-- Up to six lines: the machine, memory per owner (its largest process), then the other machines
(machine.machine_note); `ps` is read unless given. -/
def note [Monad m] [Store m] [Clock m] [Env m] [Fs m] [Proc m] (ps : Option (List Ps) := none) : m String := do
  let mm ← mem
  let ps ← match ps with | some p => pure p | none => procs
  let (agents, metas) ← Store.txn [.agent, .«meta»] fun db => (db, (db.agents, db.metas))
  let hs := holders agents ps
  let events ← if metas.any (·.k == "machines") then Store.txn [.event] fun db => (db, db.events) else pure []
  let gib (k : Int) : String := fixed (Float.ofInt k / 1048576) 1
  let mut lines := [lineOf mm]
  for h in hs.take 3 do
    lines := lines ++ [s!"  {h.agent} {gib h.kb}G{match h.top with | some t => s!" ({cut t 40} {gib h.top_kb}G)" | none => ""}"]
  if hs.length > 3 then lines := lines ++ [s!"  +{hs.length - 3} more holders"]
  return "\n".intercalate (lines ++ (← remoteLines metas events (← Clock.now)))

/-- Each process's working directory, none when no process's can be read (callers then assume every dir is in use)
(machine.cwds). -/
def cwds [Monad m] [Env m] [Fs m] [Proc m] [Sys m] : m (Option (List (Int × String))) := do
  if (← osName) == "Darwin" then  -- own processes need no sudo; others' are skipped
    let o ← Proc.output ["lsof", "-a", "-d", "cwd", "-Fpn"] none []
    let out := parseLsof ((o.map (·.stdout)).getD "")
    return if out.isEmpty then none else some out
  let root ← procRoot
  let some es ← Fs.list root | return none
  let mut out := []
  for e in es do
    if !e.isEmpty && e.all Char.isDigit then
      if let some l ← Sys.readlink s!"{root}/{e}/cwd" then out := out ++ [(((e.toNat?.getD 0 : Nat) : Int), l)]
  return some out

/-- The nearest ancestor of this process that is the claude process (its command's name holds `claude`)
(machine.claude_pid); `ps` is read unless given. -/
def claudePid [Monad m] [Proc m] [Sys m] (ps : Option (List Ps) := none) : m (Option Int) := do
  let ps ← match ps with | some p => pure p | none => procs
  let by_ := byPid ps
  let rec up : Nat → Option Ps → Option Int
    | 0, _ => none
    | n + 1, p => match p with
      | none => none
      | some p => if p.pid ≤ 1 then none else if hasSub p.comm "claude" then some p.pid else up n (by_.get? p.ppid)
  return up 64 (by_.get? (← Sys.getppid))

end SwarmLean.Machine

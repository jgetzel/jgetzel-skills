import SwarmLean.Cmd
import SwarmLean.Cmd.OpsHelp
import SwarmLean.Lib.Run
import SwarmLean.Lib.Cost

/-! `swarm run [--on M] [--env X]... cmd…` (run.cmd_run): a build or test here, or on another hc machine against a copy
of this worktree, recorded as a job. -/

namespace SwarmLean.Cmd.Run
open Args _root_.SwarmLean.Run
open Lean (Json)

/-- The `run` parser; the command (everything from the first positional or `--` on) is split off first (`split`). -/
def spec : Spec :=
  .mk "run" helpRun [] [opt "--on", { opt "--env" with maxCount := 1000000 }] [] [] none

/-- main.lua's split_run on the words after `run`: the options, and the command (`--` dropped). -/
def split (args : List String) : List String × List String :=
  let rec go (i : Nat) (fuel : Nat) : Nat :=
    match fuel, args[i]? with
    | f + 1, some x =>
      if x == "--on" || x == "--env" then go (i + 2) f
      else if x.startsWith "--on=" || x.startsWith "--env=" || x == "-h" || x == "--help" then go (i + 1) f
      else i
    | _, _ => i
  let i := go 0 (args.length + 1)
  let rest := args.drop i
  (args.take i, if rest.head? == some "--" then rest.tail else rest)

/-- run.sanitize: every character but `[%w_.-]` as `_`. -/
def sanitize (s : String) : String := s.map fun c => if c.isAlphanum || c == '_' || c == '.' || c == '-' then c else '_'

variable {m : Type → Type} [Monad m] [MonadExceptOf Exit m] [Store m] [Clock m] [Env m] [Fs m] [Proc m] [Git m] [Sys m]

/-- `.claude/swarm.json`'s `run` object, or {}. -/
def readCfg (top : String) : m Json := do
  match ((← Fs.read (joinPath top ".claude/swarm.json")).bind Json.decode).bind (Json.field · "run") with
  | some c@(.obj _) => return c
  | _ => return Json.mkObj []

/-- git's stdout, stripped, when it exits 0 (proc.git). -/
def git (args : List String) (cwd : Option String := none) : m (Option String) := return (← Git.git args cwd).map strip

/-- Tree of the working state (tracked and untracked, not ignored), written into a copy of the index; reads wt only. -/
def treeOf (wt : String) : m (Option String) := do
  let some idx ← git ["-C", wt, "rev-parse", "--path-format=absolute", "--git-path", "index"] | return none
  if (← git ["-C", wt, "rev-parse", "HEAD"]).isNone then return none
  let tmp := strip (← Sys.exec ["mktemp"] {}).stdout
  discard <| Sys.exec ["cp", "-p", idx, tmp] {}  -- keeps the index mtime, or git trusts stale stat data (racy git)
  let env := [("GIT_INDEX_FILE", some tmp), ("GIT_OPTIONAL_LOCKS", some "0")]
  discard <| Sys.exec ["git", "-C", wt, "add", "-A"] { env }
  let out := strip (← Sys.exec ["git", "-C", wt, "write-tree"] { env }).stdout
  discard <| Sys.remove tmp
  return if out == "" then none else some out

/-- `{file: blob hash}` for the plain files of `files` (one git call). -/
def hashes (top : String) (files : List String) : m (List (String × String)) := do
  let mut names := []
  for f in files do
    if (← Sys.kind (joinPath top f) false) == .file && !hasSub f "\n" then names := names ++ [f]
  let r ← Sys.exec ["git", "-C", top, "hash-object", "--stdin-paths"] { input := some ("\n".intercalate names ++ "\n") }
  return names.zip (splitlines r.stdout)

/-- A finished remote job as a history row: its wall time and the last RSS and CPU watchd read on that machine. -/
def recordRemote (who mach jid cmd repo : String) (s : Int) : m Unit := do
  let db ← Store.txn [.«meta»] fun db => (db, db)
  let ms := (db.getMeta "machines").bind (·.v) |>.bind Json.decode
  let last := ((ms.bind (Json.field · mach)).bind (Json.field · "jobs")).bind (Json.field · jid) |>.getD (Json.mkObj [])
  discard <| Cost.record { ts := ← Clock.now, machine := mach, repo, agent := who, source := "run", cmd, wall_s := s, cpu_s := (Json.fint last "cpu").getD 0, peak_kb := (Json.fint last "rss_kb").getD 0 }

/-- The job's exit as the record and the message say it: a code, or lost. -/
inductive Code | n (c : Int) | lost

/-- `swarm run …`. -/
def run (a : Parsed) : m UInt32 := do
  let argv := a.strs "argv"
  if argv.isEmpty then die "usage: swarm run [--on <machine>] [--env NAME[=VAL]]... -- <cmd…>"
  let some top0 ← git ["rev-parse", "--show-toplevel"] | die "not in a git repo"
  if top0 == "" then die "not in a git repo"
  let top := (← Sys.realpath top0).getD top0
  let common := (← git ["rev-parse", "--path-format=absolute", "--git-common-dir"]).getD ""
  let repo := sanitize (if common.endsWith "/.git" then basename (dirname common) else basename top)
  let wtname := sanitize (basename top)
  let cwd ← Env.cwd
  let cwd := (← Sys.realpath cwd).getD cwd
  let rel := if cwd == top then "." else if cwd.startsWith (top ++ "/") then (cwd.drop (top.length + 1)).toString else "."
  let cfg ← readCfg top
  let who := (← env "SWARM_NAME").getD "human"
  let line := if argv.length == 1 then argv.head! else shjoin argv
  let full := match Json.fstr cfg "prefix" with
    | some p => p ++ " " ++ (if argv.length == 1 then "sh -c " ++ shquote line else line)
    | none => line
  let jenv ← jobEnv cfg top (a.strs "env")
  let jid ← Store.txn [.«meta»] fun db =>
    let n := match db.getMeta "jobs" with | some r => ((r.v.bind parseInt).getD 0) + 1 | none => 1
    (db.setMeta "jobs" (some (d n)), d n)
  let dbp := match ← env "SWARM_DB" with | some p => p | none => common ++ "/swarm/swarm.db"
  let jobs := joinPath (joinPath (dirname dbp) "jobs") jid
  discard <| Sys.mkdirp jobs
  let logf := jobs ++ "/log"
  let task ← Store.txn [.task] fun db => (db, ((db.tasks.filter fun t => t.owner == some who && (t.state = .claimed || t.state = .blocked)).head?.map (·.id)))
  let dir := s!"{RUN_DIR}/{repo}/{wtname}"
  let on := a.str "on"
  let rec0 : List (String × Option Json) := [("machine", on.map .str), ("wt", some (.str top)), ("task", task.map fun t => Json.int t),
    ("cmd", some (.str full)), ("pid", some (Json.int (← Sys.getpid)))]
  let t0 ← Sys.nowF
  let logEv (kind : String) (data : Json) : m Unit := do
    let now ← Clock.now
    Store.txn [] fun db => (db.log now (some who) kind (some jid) (some (Json.encode data)), ())
  let finish (code : Code) (tree : Option String) (sync back : Option Float) (kept : List String) (hc : Option String) : m UInt32 := do
    let s := (← Sys.nowF) - t0 |>.floor |>.toInt64.toInt
    logEv "job-end" (obj [("machine", on.map .str), ("exit", some (match code with | .n c => Json.int c | .lost => .str "lost")),
      ("s", some (Json.int s)), ("sync_s", sync.map Lean.toJson), ("back_s", back.map Lean.toJson), ("tree", tree.map .str)])
    if let some mach := on then  -- a local job is a command under the agent's shell: watchd measures it
      try recordRemote who mach jid full repo s catch _ => pure ()
    let lines := splitlines ((← Fs.read logf).getD "")
    let tail := lines.drop (lines.length - JOB_TAIL)
    if !tail.isEmpty then Env.out ("\n".intercalate tail)
    let lost := match code with | .lost => true | _ => false
    let sec := s % 60
    Env.out (s!"job j{jid} {match code with | .n c => "exit " ++ d c | .lost => "lost"} on {on.getD "this machine"}, {fdiv s 60}m{if sec < 10 then "0" else ""}{sec}s" ++
      (match sync, back with | some x, some y => s!" (sync {fixed x 1}s, back {fixed y 1}s)" | _, _ => "") ++
      (match tree with | some t => ", tree " ++ (t.take 7).toString | none => "") ++ "; log: " ++ logf ++
      (if kept.isEmpty then "" else s!"\nkept your local edits; the job's versions of {", ".intercalate kept} are in {jobs}/kept/") ++
      (match lost, hc with | true, some h => s!"\nthe terminal {h} may still be running: `hc wait {h}` later" | _, _ => ""))
    return match code with | .lost => 255 | .n c => (c.toNat % 256).toUInt32
  let some mach := on | do
    logEv "job-start" (obj rec0)
    let tree ← treeOf top
    let r ← Sys.exec ["sh", "-c", full] { env := jenv.map fun (k, v) => (k, some v), stdoutFile := some logf }
    finish (.n r.code.toNat) tree none none [] none
  let ms ← hcMachines
  let mc := ms.lookup mach
  if mc.bind (Json.fstr · "state") != some "connected" then
    Env.err s!"swarm: machine {mach} is {match mc with | some x => (Json.fstr x "state").getD "nil" | none => "not in `hc machine ls`"}; the job never ran. Pick another (see the machine note)."
    throw (Exit.mk 255)
  let sshv ← sshCmd
  let ssh := shjoin sshv
  let tgt := ((mc.bind (Json.fstr · "target")).getD "nil")
  let now ← Clock.now
  let live ← Store.txn [.event] fun db => (db, liveJobs db now)
  let mut busy := 0
  for j in live do
    if j.s "machine" == some mach && j.s "wt" == some top then
      if let some p := (Json.field j.data "pid").bind Json.int? then
        if ← Sys.pidAlive p then busy := busy + 1
  let src := dir ++ "/src" ++ (if busy > 0 then "." ++ toString (busy + 1) else "")
  let lsOut := ((← Git.git ["-C", top, "ls-files", "-z", "-c", "-o", "--exclude-standard"] none).getD "")
  let files := (lsOut.splitOn "\x00").filter (· ≠ "")
  let before ← hashes top files
  let mk ← Sys.exec (sshv ++ [tgt, "mkdir -p " ++ shquote src]) {}
  if mk.code != 0 then
    let last := splitlines (strip mk.stderr)
    Env.err s!"swarm: sync to {mach} failed (mkdir exit {mk.code}: {last.getLastD "?"}); the job never ran."
    throw (Exit.mk 255)
  let rs ← Sys.exec ["rsync", "-rlpD", "--checksum", "--delete", "--exclude=.git", "--filter=:- .gitignore",
    "-e", ssh, top ++ "/", tgt ++ ":" ++ src ++ "/"] {}
  let sync := (← Sys.nowF) - t0
  if rs.code != 0 then
    let last := splitlines (strip rs.stderr)
    Env.err s!"swarm: sync to {mach} failed (rsync exit {rs.code}: {last.getLastD "?"}); the job never ran."
    throw (Exit.mk 255)
  let exports := ((jenv.map fun (k, v) => k ++ "=" ++ shquote v).mergeSort (· ≤ ·))
  let setO : List (String × String) := match Json.field cfg "set" with
    | some (.obj kv) => kv.toList.map fun (k, v) => (k, (Json.str? v).getD "")
    | _ => []
  let exports := exports ++ ((setO.mergeSort fun x y => x.1 ≤ y.1).map fun (k, v) =>
    k ++ "=\"" ++ v.replace "{dir}" ("$HOME/" ++ dir) ++ "\"")
  let metaD := s!"\"$HOME/{dir}/jobs/{jid}\""
  let script := "; ".intercalate [
    s!"mkdir -p {metaD} && cd \"$HOME/{src}\" || exit 255", "[ -d .git ] || git init -q",
    s!"git add -A && git write-tree > {metaD}/tree",
    s!"\{ (cd {shquote rel} && {if exports.isEmpty then "" else "export " ++ " ".intercalate exports ++ " && "}{full}); echo $? > {metaD}/rc; } 2>&1 | tee {metaD}/log",
    s!"git ls-files -z -m -o --exclude-standard > {metaD}/files",
    s!"exit \"$(cat {metaD}/rc 2>/dev/null || echo 255)\""]
  let name := String.ofList (((who ++ "-j" ++ jid).toLower.toList.map fun c => if c.isLower || c.isDigit || c == '_' || c == '-' then c else '-').take 32)
  let hcrun := ["hc", "run", "--on", mach, "--bg", "--json", "--no-notify", "--name", name, "--label", "swarm-agent=" ++ who,
    "--label", "swarm-job=" ++ jid, "--label", s!"swarm-wt={repo}/{wtname}"] ++
    (match task with | some t => ["--label", "swarm-task=" ++ d t] | none => []) ++ ["sh", "-c", script]
  let o := (← Proc.output hcrun none []).bind fun r => if r.code == 0 then Json.decode r.stdout else none
  let some addr := o.bind (Json.fstr · "address") | do
    Env.err s!"swarm: `hc run --on {mach}` failed; the job never ran."
    throw (Exit.mk 255)
  logEv "job-start" (obj (rec0 ++ [("dir", some (.str dir)), ("hc", some (.str addr))]))
  let mut w : Option Json := none
  repeat
    let x := (← Proc.output ["hc", "wait", addr, "--json", "--timeout", "600"] none []).bind fun r =>
      if r.code == 0 then Json.decode r.stdout else none
    match x with
    | some x@(.obj _) => if (Json.field x "ended").any (· != .bool false) then w := some x; break
    | _ => break
  let some wj := w | finish .lost none (some sync) none [] (some addr)
  let code : Code := match Json.fint wj "exit_code" with
    | some c => .n c
    | none => match Json.fint wj "signal" with | some sg => .n (128 + sg) | none => .lost
  let tb ← Sys.nowF
  let rsync (args : List String) : m Unit := do discard <| Sys.exec (["rsync", "-a", "-e", ssh] ++ args) {}
  rsync [s!"{tgt}:{dir}/jobs/{jid}/", jobs ++ "/"]
  let back := (((← Fs.read (jobs ++ "/files")).getD "").splitOn "\x00").filter (· ≠ "")
  let mut kept := []
  if !back.isEmpty then
    let stage := jobs ++ "/kept"
    rsync ["--from0", "--files-from=" ++ jobs ++ "/files", s!"{tgt}:{src}/", stage ++ "/"]
    let nowH ← hashes top back
    for f in back do
      if (← Sys.kind (stage ++ "/" ++ f) false) != .none then
        let here := (← Sys.kind (joinPath top f) false) != .none
        if nowH.lookup f == before.lookup f && here == (before.lookup f).isSome then  -- untouched here since the sync
          discard <| Sys.mkdirp (dirname (joinPath top f))
          discard <| Sys.exec ["mv", "-f", stage ++ "/" ++ f, joinPath top f] {}
        else kept := kept ++ [f]
  let home := (← Env.var "HOME").getD ""
  for b in Json.items ((Json.field cfg "bring_back").getD .null) do  -- ~/x: the same path on both machines; else under the tree
    let some b := Json.str? b | continue
    if b.startsWith "~/" then rsync [tgt ++ ":" ++ (b.drop 2).toString, home ++ (b.drop 1).toString]
    else rsync [s!"{tgt}:{src}/{b}", joinPath top b]
  let tree := (← Fs.read (jobs ++ "/tree")).map strip
  discard <| Proc.output ["hc", "rm", addr] none []
  finish code tree (some sync) (some ((← Sys.nowF) - tb)) kept (some addr)

/-- The group: run. -/
def group : Group m where
  specs := [("run", spec)]
  run := run

end SwarmLean.Cmd.Run

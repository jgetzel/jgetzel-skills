import SwarmLean.Db.Spawn
import SwarmLean.Lib.Agents
import SwarmLean.Lib.Ci
import SwarmLean.Lib.Machine
import SwarmLean.Lib.Workspaces

/-! watchd.lua's spawn: the reservation, the agent's worktree, its brief and settings, launch.sh, and undoing all of
it when the launch fails (cmd_spawn, launch_agent). -/

namespace SwarmLean.Spawn
open Agents

variable {m : Type → Type} [Monad m] [MonadExceptOf Exit m] [Store m] [Clock m] [Env m] [Fs m] [Proc m] [Git m] [Sys m]

/-- The db file (db.dbpath): $SWARM_DB, else swarm/swarm.db in the repo's git common dir. -/
def dbPath : m String := do
  if let some p ← env "SWARM_DB" then return p
  match ← Git.git ["rev-parse", "--path-format=absolute", "--git-common-dir"] none with
  | some dir => if strip dir != "" then return joinPath (joinPath (strip dir) "swarm") "swarm.db" else die "not in a git repo and SWARM_DB is unset"
  | none => die "not in a git repo and SWARM_DB is unset"

/-- The swarm/ directory (the launcher's SWARM_HERE): $SWARM_HERE, else the one above this binary. -/
def swarmHere : m (Option String) := do
  if let some h ← env "SWARM_HERE" then return some h
  Proc.launcherDir

/-- Writes agent `name`'s settings file and runs launch.sh for it in `cwd`, in the swarm's Herdr space: launch.sh's
output (none on failure) and the first line of its stderr (watchd.launch_agent). -/
def launchAgent (name brief model : String) (effort cwd : Option String) : m (Option String × String) := do
  let here := (← swarmHere).getD "."
  let self_ := joinPath here "swarm"
  let dbp ← dbPath
  let some tpl ← Fs.read (joinPath here "settings.template.json") | die s!"no settings.template.json in {here}"
  let sd := joinPath (dirname dbp) "agents"
  discard <| Sys.mkdirp sd
  let sf := joinPath sd (name ++ ".settings.json")
  let bindir := joinPath (dirname dbp) "bin"  -- puts `swarm` on the agent's PATH
  discard <| Sys.mkdirp bindir
  if (← Sys.kind (joinPath bindir "swarm") false) == .none then
    discard <| Proc.output ["ln", "-s", self_, joinPath bindir "swarm"] none []
  let path := (← Env.var "PATH").getD ""
  let text := ((((tpl.replace "{{SWARM}}" self_).replace "{{DB}}" dbp).replace "{{NAME}}" name).replace "{{PATH}}" (bindir ++ ":" ++ path))
  if !(← Fs.write sf text) then die s!"can't write {sf}"
  let launch ← match ← env "SWARM_LAUNCH" with
    | some l => pure l
    | none => pure (joinPath (joinPath (joinPath here "..") "relaunch") "launch.sh")
  let argv := [launch, name, "tab", brief, "--permission-mode", "auto", "--model", model, "--settings", sf] ++
    (match effort with | some e => ["--effort", e] | none => [])
  let space ← Store.txn [.«meta»] fun db => (db, (db.getMeta "space").bind (·.v))
  let o ← Proc.output argv cwd (match space with | some s => [("SWARM_SPACE", s)] | none => [])
  let err := match o with | some o => ((strip o.stderr).splitOn "\n").headD "" | none => ""
  let mut out := match o with | some o => if o.code == 0 then some o.stdout else none | none => none
  if out.isNone then  -- launch.sh can fail after hc started the agent: keep a live terminal by that name
    for x in (← hcTerminals).getD [] do
      if x.name == some name && x.state == some "live" && x.address.isSome then out := x.address; break
  return (out, err)

/-- What `swarm spawn` was given. -/
structure Args where
  name : String
  model : String := "sonnet"
  effort : Option String := none
  stay : Option String := none
  taskId : Option Int := none
  role : Option String := none
  attach : Option String := none
  /-- the words after the options: text for the brief -/
  task : List String := []
  /-- auto-spawn: the head of the pool, checked in the claim's transaction -/
  top : Option (Db → Option Int) := none

/-- Prints a refusal as main.lua does (a die's `swarm: …`, the others as they are) and exits 1. -/
def refuse (e : Refusal) : m α := do
  match e with
  | .die msg => die msg
  | .refused msg | .lost msg => Env.err msg; throw (Exit.mk 1)

/-- `swarm spawn` (watchd.cmd_spawn): reserve (and claim), make or link the worktree, write the brief, launch; any
failure after the reservation undoes it. A refused reservation comes back unprinted (auto-spawn tells them apart), a
launch that failed as `some` launch.sh's reason (after `swarm: launch.sh failed`); any other failure exits. -/
def spawnE (a : Args) : m (Except Refusal (Option String)) := do
  let name := a.name
  let task := " ".intercalate a.task
  if a.taskId.isNone && task == "" then
    die "usage: swarm spawn <name> [--model M] [--effort E] [--role R] [--stay S] [--task N] [--attach WT] -- <task>"
  let spawner := (← env "SWARM_NAME").getD HUMAN
  orDie (notHuman name)
  let envComms ← env "SWARM_COMMS"
  let cwd ← Env.cwd
  let now ← Clock.now
  let r ← match a.taskId with
    | none => Store.txn [.agent, .«meta», .cursor] fun db =>
        let (db, e) := reserve db envComms name cwd (some a.model) now
        (db, e.map fun () => none)
    | some tid => Store.txn [.agent, .«meta», .cursor, .task] fun db =>
        let (db, e) := reserveTask db envComms name cwd tid (some a.model) now a.top
        (db, e.map some)
  let r ← match r with
    | .ok r => pure r
    | .error e =>
      if let .refused _ := e then Store.txn [] fun db => (db.log now (some spawner) "spawn-refused" none (some name), ())
      return .error e
  let undo (wt : Option (String × String)) : m Unit := do
    if let some (p, b) := wt then Workspaces.discardWs name p b a.attach.isNone
    let now ← Clock.now
    Store.txn [.agent, .task] fun db => (unreserve db name r now, ())
  -- the role, the stay, the task line and the worktree: a failure leaves no worktree to discard
  let (task, wt) ← tryCatchThe Exit (do
    let now ← Clock.now
    if let some role := a.role then discard <| Store.txn [.agent] fun db => setRole db name role now
    if let some s := a.stay then Store.txn [.agent] fun db => (db.setAgent name ({ · with stay := some (oneLine s) }), ())
    let mut task := task
    let mut wt : Option (String × String) := none
    if let (some tid, some r) := (a.taskId, r) then
      task := s!"Board task #{d tid}: {r.title.getD ""}. It is claimed for you; `swarm task show {d tid}` prints it." ++
        (match py r.body with | some b => "\n\n" ++ b | none => "") ++ (if task != "" then "\n\n" ++ task else "")
    if a.taskId.isSome || a.attach.isSome then
      match a.attach with
      | some at_ =>
        let (path, br, _) ← Workspaces.attach name at_
        wt := some (path, br.getD "")
        task := task ++ s!"\n\nYou are attached READ-ONLY to {path} (branch {br.getD "nil"}): read and run, never edit or commit there. Make your own worktree for changes."
      | none =>
        let row ← Store.txn [.task] fun db => (db, a.taskId.bind db.find)
        let (path, br, base) ← Workspaces.create name (row.getD { id := 0 }) none
        wt := some (path, br)
        task := task ++ s!"\n\nYour worktree: {path} (branch {br}, base {base}). Work only there. Never check out {base}: land by a fast-forward of it from this branch (`git push . HEAD:{base}`, or a PR for a remote base)."
    pure (task, wt)) fun e => do undo none; throw e
  let out ← tryCatchThe Exit (do
    let here := (← swarmHere).getD "."
    let db ← Store.txn [.agent, .«meta»] fun db => (db, db)
    let roster := (← splitAgents db).1.map fun x =>
      s!"{x.name} ({x.status.getD "None"}{match x.role with | some r => ", " ++ r | none => ""})"
    let mut brief := ((← Fs.read (joinPath here "brief.md")).getD "") ++
      s!"\n\n---\nYour name: {name}. Roster: {if roster.isEmpty then "nobody yet" else ", ".intercalate roster}.\nYour area and first task:\n{task}\n"
    brief := brief ++ "\n" ++ ((Ci.FLOW_LINE ((← Ci.flow (wt.map (·.1))).getD "post-merge")).getD "") ++ "\n"
    if let some rules := db.getMeta "rules" then
      brief := brief ++ s!"\nRules for this repo, from the communicator:\n{rules.v.getD "None"}\n"
    launchAgent name brief a.model a.effort (wt.map (·.1))) fun e => do undo wt; throw e
  let (some out, _) := out | do undo wt; Env.err "swarm: launch.sh failed"; return .ok (some out.2)
  let addr := (splitlines (strip out)).getLastD ""
  let now ← Clock.now
  Store.txn [.agent] fun db =>
    let db := db.setAgent name fun x => if x.hc.isNone then { x with hc := some addr } else x
    (db.log now (some spawner) "spawn" none (some name), ())
  Env.out s!"spawned {name} at {strip out}"
  Env.out (← Machine.note)
  return .ok none

/-- `swarm spawn`: `spawnE`, a refusal printed and a failed launch exiting 1. -/
def spawn (a : Args) : m Unit := do
  match ← spawnE a with
  | .error e => refuse e
  | .ok (some _) => throw (Exit.mk 1)
  | .ok none => pure ()

end SwarmLean.Spawn

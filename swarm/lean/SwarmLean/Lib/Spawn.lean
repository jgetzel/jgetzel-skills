import SwarmLean.Db.Spawn
import SwarmLean.Lib.Agents
import SwarmLean.Lib.Ci
import SwarmLean.Lib.Machine
import SwarmLean.Lib.Workspaces
import SwarmLean.DbPath

/-! watchd.lua's spawn: the reservation, the agent's worktree, its brief and settings, launch.sh, and undoing all of
it when the launch fails (cmd_spawn, launch_agent). -/

namespace SwarmLean.Spawn
open Agents

variable {m : Type → Type} [Monad m] [MonadExceptOf Exit m] [Store m] [Clock m] [Env m] [Fs m] [Proc m] [Git m] [Sys m]

/-- The labels hc keeps on terminal `addr`: its Herdr space and the db it is the communicator of (agents.hc_info). -/
def hcLabels (addr : String) : m (Option String × Option String) := do
  let o ← Proc.output ["hc", "get", addr] none []
  let j := match o with | some o => if o.code == 0 then (Lean.Json.parse o.stdout).toOption else none | none => none
  let l := (j.bind fun j => (j.getObjVal? "labels").toOption).getD .null
  return ((l.getObjValAs? String "herdr.space").toOption, (l.getObjValAs? String "swarm.comms").toOption)

/-- The db file, or none (`DbPath.choose`): $SWARM_DB, else the repo's git common dir, else the db this terminal is the
communicator of (its `swarm.comms` label), if that db is there. -/
def dbPath? : m (Option String) := do
  let envDb ← env "SWARM_DB"
  if (py envDb).isSome then return DbPath.choose envDb none none
  let git ← Git.git ["rev-parse", "--path-format=absolute", "--git-common-dir"] none
  if (py (git.map strip)).isSome then return DbPath.choose none git none
  let some h ← env "HC_TERMINAL_ID" | return none
  let label := (← hcLabels h).2
  let label ← match label with
    | some p => pure (if (← Sys.kind p true) != .none then some p else none)
    | none => pure none
  return DbPath.choose none none label

/-- The db file (db.dbpath): `dbPath?`, else die as the store's connect does (Real.dbPath, which names the swarms
under the cwd). -/
def dbPath : m String := do
  match ← dbPath? with
  | some p => return p
  | none => die "not in a git repo and SWARM_DB is unset"

/-- The swarms on this machine (UI-SPEC.md, "New swarm CLI output" 2): one file per db, written by its watchd and by
each join and spawn, in $XDG_STATE_HOME (else ~/.local/state)/swarm/swarms. -/
def registryDir : m String := do
  let x ← match ← env "XDG_STATE_HOME" with | some x => pure x | none => pure (((← env "HOME").getD "") ++ "/.local/state")
  return x ++ "/swarm/swarms"

/-- Db `p`'s registry file: its path with `/` as `%`. -/
def registryFile (p : String) : m String := return s!"{← registryDir}/{p.replace "/" "%"}.json"

/-- The folder a swarm's commands run from: the repo of a default db (`DbPath.repoOf`), else the cwd's repo, else the
cwd. -/
def folderOf (db : String) : m String := do
  if let some f := DbPath.repoOf db then return f
  return (py ((← Git.git ["rev-parse", "--show-toplevel"] none).map strip)).getD (← Env.cwd)

/-- The swarm's tag: its communicator's name without `-comms` (as the rail draws it). -/
def tagOf (comms : String) : String :=
  let c := (comms.toList.reverse.dropWhile Char.isDigit).reverse
  let c := if String.ofList c |>.endsWith "comms" then c.take (c.length - 5) else c
  String.ofList (c.reverse.dropWhile (· == '-')).reverse

/-- A registry entry's terminals: those of the agents that joined or were spawned into it. -/
def regTerms (j : Lean.Json) : List String := ((Json.field j "terms").map Json.items |>.getD []).filterMap Json.str?

/-- Registers this db's swarm (`registered`): `pid` a starting watchd's (none keeps the entry's), `term` a terminal
that joined or was spawned into it, added to the entry's live ones (all kept when hc does not answer). -/
def register (comms term : Option String) (pid : Option Int) : m Unit := do
  let db ← dbPath
  let reg ← registryFile db
  let old := (← Fs.read reg).bind Json.decode
  let up := ((← hcTerminals).map fun ts => ts.filterMap fun x => if x.state == some "live" then x.address else none)
  let mut terms := (old.map regTerms).getD [] |>.filter fun t => up.all (·.contains t)
  if let some t := term then if !terms.contains t then terms := terms ++ [t]
  let comms := comms.orElse fun _ => old.bind (Json.fstr · "comms")
  let now ← Clock.now
  let pid' := pid.orElse fun _ => old.bind (Json.fint · "pid")
  let started := if pid.isSome then now else (old.bind (Json.fint · "started")).getD now
  discard <| Sys.mkdirp (← registryDir)
  discard <| Fs.write reg (Json.encode (Lean.Json.mkObj [("db", .str db), ("folder", .str (← folderOf db)),
    ("tag", match comms with | some c => .str (tagOf c) | none => .null), ("comms", match comms with | some c => .str c | none => .null),
    ("pid", match pid' with | some p => Json.int p | none => .null), ("started", Json.int started),
    ("terms", .arr (terms.map Lean.Json.str).toArray)]))

/-- An exiting watchd `pid`'s end of its registration: the entry keeps its terminals with no pid, or goes with none. -/
def unregisterPid (pid : Int) : m Unit := do
  let reg ← registryFile (← dbPath)
  let some j := (← Fs.read reg).bind Json.decode | return
  if Json.fint j "pid" != some pid then return
  if (regTerms j).isEmpty then discard <| Sys.remove reg
  else discard <| Fs.write reg (Json.encode (j.setObjVal! "pid" .null))

/-- Each registered swarm whose watchd runs (`watchd` true) or, with none, that a live terminal joined or was spawned
into (`watchd` false), by folder. An entry with neither goes; one hc can't judge (it does not answer) stays unlisted. -/
def registered : m (List Lean.Json) := do
  let dir ← registryDir
  let mut out : List Lean.Json := []
  let mut up : Option (Option (List String)) := none  -- hc ls, read once and only if needed
  for f in ((← Fs.list dir).getD []).filter (·.endsWith ".json") do
    let path := dir ++ "/" ++ f
    let some j := (← Fs.read path).bind Json.decode | continue
    if ← match Json.fint j "pid" with | some p => Sys.pidAlive p | none => pure false then
      out := out ++ [j.setObjVal! "watchd" (.bool true)]; continue
    let ts := regTerms j
    if ts.isEmpty then discard <| Sys.remove path; continue
    if up.isNone then up := some ((← hcTerminals).map fun ts => ts.filterMap fun x => if x.state == some "live" then x.address else none)
    match up.join with
    | none => pure ()
    | some live =>
      if ts.any live.contains then out := out ++ [(j.setObjVal! "pid" .null).setObjVal! "watchd" (.bool false)]
      else discard <| Sys.remove path
  return out.mergeSort fun x y => (Json.fstr x "folder").getD "" ≤ (Json.fstr y "folder").getD ""

/-- The swarm/ directory (the launcher's SWARM_HERE): $SWARM_HERE, else the one above this binary. -/
def swarmHere : m (Option String) := do
  if let some h ← env "SWARM_HERE" then return some h
  Proc.launcherDir

/-- The skills a lean agent keeps. -/
def LEAN_SKILLS : List String := ["hc", "herdr-app", "swarm", "terse-comments", "code-review"]

/-- Claude Code's bundled skills (2.1.319). -/
def BUNDLED_SKILLS : List String :=
  ["dataviz", "artifact-design", "artifact-diagramming", "artifact-capabilities", "update-config", "keybindings-help",
   "simplify", "fewer-permission-prompts", "loop", "schedule", "claude-api", "workflow-authoring", "claude-in-chrome",
   "run", "plugin-authoring", "init", "security-review", "code-review"]

/-- The lean profile's settings (SKILL.md, "Lean profile"): every installed plugin off, claude.ai's synced skills and
Workflows off, and each user, project (in `cwd`) and bundled skill but LEAN_SKILLS off. -/
def leanSettings (cwd : String) : m (List (String × Lean.Json)) := do
  let cfg ← match ← env "CLAUDE_CONFIG_DIR" with | some c => pure c | none => pure (((← env "HOME").getD "") ++ "/.claude")
  let plugins := match ((← Fs.read (cfg ++ "/plugins/installed_plugins.json")).bind Json.decode).bind (Json.field · "plugins") with
    | some (.obj kv) => kv.keys
    | _ => []
  let mut skills := BUNDLED_SKILLS
  for dir in [cfg ++ "/skills", cwd ++ "/.claude/skills"] do skills := skills ++ ((← Fs.list dir).getD [])
  let off := skills.eraseDups.filter (!LEAN_SKILLS.contains ·)
  return [("enabledPlugins", Lean.Json.mkObj (plugins.map (·, Lean.Json.bool false))),
          ("skillOverrides", Lean.Json.mkObj (off.map (·, Lean.Json.str "off"))),
          ("syncClaudeAiSkills", Lean.Json.bool false), ("disableWorkflows", Lean.Json.bool true)]

/-- Writes agent `name`'s settings file and runs launch.sh for it in `cwd`, in the swarm's Herdr space: launch.sh's
output (none on failure) and the first line of its stderr (watchd.launch_agent). Unless `full`, the agent gets the lean
profile: `leanSettings` and no MCP servers. -/
def launchAgent (name brief model : String) (effort cwd : Option String) (full : Bool) : m (Option String × String) := do
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
  let text ← if full then pure text else do
    let some j := Json.decode text | die s!"settings.template.json in {here} is not JSON"
    pure (Json.encode ((← leanSettings (cwd.getD (← Env.cwd))).foldl (fun j (k, v) => j.setObjVal! k v) j))
  if !(← Fs.write sf text) then die s!"can't write {sf}"
  let launch ← match ← env "SWARM_LAUNCH" with
    | some l => pure l
    | none => pure (joinPath (joinPath (joinPath here "..") "relaunch") "launch.sh")
  let argv := [launch, name, "tab", brief, "--permission-mode", "auto", "--model", model, "--settings", sf] ++
    (match effort with | some e => ["--effort", e] | none => []) ++
    (if full then [] else ["--strict-mcp-config", "--no-chrome"])
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
  /-- the ref the worktree starts from (default: spawn.base of .claude/swarm.json, else the landing base) -/
  base : Option String := none
  /-- every skill, plugin and connector (`--full`), not the lean profile -/
  full : Bool := false
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
    die "usage: swarm spawn <name> [--model M] [--effort E] [--role R] [--stay S] [--task N] [--attach WT] [--full] -- <task>"
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
    Store.txn [.agent, .task, .lock] fun db => (unreserve db name r now, ())
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
        Bases.warnBadConfig ["base", "spawn.base"] none
        let (path, br, base) ← Workspaces.create name (row.getD { id := 0 }) none a.base
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
    launchAgent name brief a.model a.effort (wt.map (·.1)) a.full) fun e => do undo wt; throw e
  let (some out, _) := out | do undo wt; Env.err "swarm: launch.sh failed"; return .ok (some out.2)
  let addr := (splitlines (strip out)).getLastD ""
  let now ← Clock.now
  Store.txn [.agent] fun db =>
    let db := db.setAgent name fun x => if x.hc.isNone then { x with hc := some addr } else x
    (db.log now (some spawner) "spawn" none (some name), ())
  if addr != "" then register none (some addr) none
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

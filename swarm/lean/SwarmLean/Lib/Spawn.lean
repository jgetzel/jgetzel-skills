import SwarmLean.Db.Spawn
import SwarmLean.Lib.Agents
import SwarmLean.Lib.Ci
import SwarmLean.Lib.Machine
import SwarmLean.Lib.Workspaces
import SwarmLean.Lib.Msgs
import SwarmLean.Db.Notes
import SwarmLean.Lib.Swarms

/-! watchd.lua's spawn: the reservation, the agent's worktree, its brief and settings, launch.sh, and undoing all of
it when the launch fails (cmd_spawn, launch_agent). -/

namespace SwarmLean.Spawn
open Agents

variable {m : Type → Type} [Monad m] [MonadExceptOf Exit m] [Store m] [Clock m] [Env m] [Fs m] [Proc m] [Git m] [Sys m]

/-- The machine's db (`Swarms.dbPath`). -/
def dbPath : m String := Swarms.dbPath

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

/-- The Herdr space of swarm `group`'s communicator: its terminal's `herdr.space` label (the window labels every terminal
it shows); none without a live bound communicator, the label or hc. -/
def commsSpace (group : String) : m (Option String) := do
  if group == "" then return none
  let some c := ((← Swarms.list).find? (·.name == group)).bind (·.comms) | return none
  let some h := (← Store.view [Sels.agent c] (·.agent c)).bind fun a => if a.ended.isNone then py a.hc else none
    | return none
  let o ← Proc.output ["hc", "get", h] none []
  let j := match o with | some o => if o.code == 0 then (Lean.Json.parse o.stdout).toOption else none | none => none
  let l := (j.bind fun j => (j.getObjVal? "labels").toOption).getD .null
  return py (l.getObjValAs? String "herdr.space").toOption

/-- Writes agent `name`'s settings file and runs launch.sh for it in `cwd`: launch.sh's
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
  -- the swarm the spawner acts on (the real store exports it once resolved) goes into the agent's settings
  let group := (← env "SWARM").getD ""
  let text := (((((tpl.replace "{{SWARM}}" self_).replace "{{DB}}" dbp).replace "{{NAME}}" name).replace "{{GROUP}}" group).replace "{{PATH}}" (bindir ++ ":" ++ path))
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
  -- the tab opens in the swarm's space, its communicator's, not the spawner's: watchd spawns from a hidden terminal
  -- with no space (model README row 24); launch.sh reads SWARM_SPACE first
  let scope ← Store.view [] (·.swarm)
  let space ← match ← env "SWARM_SPACE" with
    | some s => pure (some s)
    | none => commsSpace (if group != "" then group else scope)
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
  /-- auto-spawn: the head of the pool, checked in the claim's transaction on what `reserveTxn` reads (the tasks not
  done, the live agents with the cursors their stops wait on, the staffing knobs) -/
  top : Option (Db → Option Int) := none

/-- Prints a refusal as main.lua does (a die's `swarm: …`, the others as they are) and exits 1. -/
def refuse (e : Refusal) : m α := do
  match e with
  | .die msg => die msg
  | .refused msg | .lost msg => Env.err msg; throw (Exit.mk 1)

/-- The reservation (`reserve`, with task `tid` `reserveTask`) and the task's held notes, as one transaction: it reads the
live agents, `name`'s row of any swarm (names are the machine's: one live anywhere is refused) and cursor, the staffing
knobs and the next message id; with a task, the task and its deps (with `top`, every task not done: the pool), the
agents their stops wait on (in any swarm) and their cursors, and the task's unread notes. An ended row of another swarm
named `name` is left out of the slice, so the reservation inserts the name and the insert moves it here (`scopeStmts`). -/
def reserveTxn (envComms : Option String) (name cwd : String) (model : Option String) (now : Int) (tid : Option Int)
    (top : Option (Db → Option Int)) : Txn (Except Refusal (Option Task × List Msg)) := do
  let own := (← Txn.slice [Sels.agent name]).agents
  let moved (db : Db) : Db :=
    if own.isEmpty then { db with agents := db.agents.filter fun a => a.name != name || a.ended.isNone } else db
  let upd (ss : List Sel) (f : Db → Db × Except Refusal (Option Task × List Msg)) :
      Txn (Except Refusal (Option Task × List Msg)) :=
    Txn.step ss [.msg] fun d => let d := moved d; let (d', a) := f d; (slicePlan d d', a)
  let base := [Sels.live, { Sels.agent name with inScope := false }, Sels.cursor name, Sels.metas Sels.LIMIT_KEYS]
  match tid with
  | none =>
    upd base fun db =>
      let (db, e) := reserve db envComms name cwd model now
      (db, e.map fun () => (none, []))
  | some tid =>
    let box := Notes.box tid
    let ts : Sel := if top.isSome then { table := .task, cond := .or (.ne "state" (.text "done")) (.eq "id" (.int tid)) }
      else Sels.task tid
    let d ← Txn.slice [ts, Sels.cursor box, Sels.live]
    let deps := ((d.find tid).map Tasks.depsOf).getD []
    let stops := (d.tasks.filterMap fun t => py t.stop_to).eraseDups
    -- a stop holder may be another swarm's agent (board #124)
    let holders : List Sel := if stops.isEmpty then [] else
      [{ table := .agent, cond := .oneOf "name" (stops.map .text), inScope := false }]
    let ours := d.agents.map (·.name)
    upd (base ++ holders ++ [ts, Sels.tasks deps, Sels.cursors stops, Sels.cursor box,
        Sels.unreadPast box (Msgs.cursorOf d box)])
      fun db =>
        let (db, e) := reserveTaskAmong ours db envComms name cwd tid model now top
        (db, e.map fun r => (some r, Notes.held db tid))

/-- `swarm spawn` (watchd.cmd_spawn): reserve (and claim), make or link the worktree, write the brief, launch; any
failure after the reservation undoes it. A refused reservation comes back unprinted (auto-spawn tells them apart), a
launch that failed as `some` launch.sh's reason (after `swarm: launch.sh failed`); any other failure exits. -/
def spawnE (a : Args) : m (Except Refusal (Option String)) := do
  let name := a.name
  let task := " ".intercalate a.task
  if a.taskId.isNone && task == "" then
    die "usage: swarm spawn <name> [--model M] [--effort E] [--role R] [--stay S] [--task N] [--attach WT] [--full] -- <task>"
  let spawner := (← env "SWARM_NAME").getD HUMAN
  orDie (agentName name)
  let envComms ← env "SWARM_COMMS"
  let cwd ← Env.cwd
  let now ← Clock.now
  -- with a task: its held notes (board #202), read here for the brief and marked given once the launch succeeds
  let r ← Store.run (reserveTxn envComms name cwd (some a.model) now a.taskId a.top)
  let (r, notes) ← match r with
    | .ok r => pure r
    | .error e =>
      if let .refused _ := e then Store.run (Txn.exec [logStmt now (some spawner) "spawn-refused" none (some name)])
      return .error e
  let undo (wts : List (String × String)) : m Unit := do
    for (p, b) in wts do Workspaces.discardWs name p b a.attach.isNone
    let now ← Clock.now
    Store.run (Txn.update (Sels.release name) [] fun db => (unreserve db name r now, ()))
  -- the role, the stay, the task line and the worktrees (one per repo of the task): a failure discards those made
  let (task, wts) ← tryCatchThe Exit (do
    let now ← Clock.now
    if let some role := a.role then discard <| Store.run (Txn.update [Sels.live, Sels.agent name] [] (setRole · name role now))
    if let some s := a.stay then
      Store.run (Txn.update [Sels.agent name] [] fun db => (db.setAgent name ({ · with stay := some (oneLine s) }), ()))
    let mut task := task
    let mut wts : List (String × String) := []
    if let (some tid, some r) := (a.taskId, r) then
      let held ← Msgs.fmtMsgs notes
      task := s!"Board task #{d tid}: {r.title.getD ""}. It is claimed for you; `swarm task show {d tid}` prints it." ++
        (match py r.body with | some b => "\n\n" ++ b | none => "") ++ (if task != "" then "\n\n" ++ task else "") ++
        (if notes.isEmpty then "" else s!"\n\nNotes left on #{d tid} for its next owner:\n{held}")
    if a.taskId.isSome || a.attach.isSome then
      match a.attach with
      | some at_ =>
        let (path, br, _) ← Workspaces.attach name at_
        wts := [(path, br.getD "")]
        task := task ++ s!"\n\nYou are attached READ-ONLY to {path} (branch {br.getD "nil"}): read and run, never edit or commit there. Make your own worktree for changes."
      | none =>
        let row ← Store.view (a.taskId.map Sels.task).toList fun db => a.taskId.bind db.find
        let repos ← match a.taskId with
          | some tid => Swarms.taskRepos tid
          | none => pure []
        if repos.isEmpty then
          task := task ++ "\n\nThis task touches no repo: no worktree was made for it."
        let mut lines : List String := []
        for (repo, _) in repos do
          Bases.warnBadConfig ["base", "spawn.base"] (some repo)
          let done := wts
          let (path, br, base) ← tryCatchThe Exit (Workspaces.create name (row.getD { id := 0 }) (some repo) a.base)
            fun e => do for (p, b) in done do Workspaces.discardWs name p b true
                        throw e
          wts := wts ++ [(path, br)]
          lines := lines ++ [s!"{path} (branch {br}, base {base}, repo {repo})"]
          if repos.length == 1 then
            task := task ++ s!"\n\nYour worktree: {path} (branch {br}, base {base}). Work only there. Never check out {base}: land by a fast-forward of it from this branch (`git push . HEAD:{base}`, or a PR for a remote base)."
        if repos.length > 1 then
          task := task ++ "\n\nYour worktrees, one per repo of the task:\n" ++ "\n".intercalate (lines.map ("- " ++ ·)) ++
            "\nWork only there. Never check out a base: land each by a fast-forward of its base from its branch (`git push . HEAD:<base>`, or a PR for a remote base)."
    pure (task, wts)) fun e => do undo []; throw e
  let out ← tryCatchThe Exit (do
    let here := (← swarmHere).getD "."
    let db ← Store.view [Sels.live, Sels.metas ["rules"]] id
    let roster := (← splitAgents db).1.map fun x =>
      s!"{x.name} ({(x.status.map (·.text)).getD "None"}{match x.role with | some r => ", " ++ r | none => ""})"
    let mut brief := ((← Fs.read (joinPath here "brief.md")).getD "") ++
      s!"\n\n---\nYour name: {name}. Roster: {if roster.isEmpty then "nobody yet" else ", ".intercalate roster}.\nYour area and first task:\n{task}\n"
    brief := brief ++ "\n" ++ ((Ci.FLOW_LINE ((← Ci.flow (wts.head?.map (·.1))).getD "post-merge")).getD "") ++ "\n"
    if let some rules := db.getMeta "rules" then
      brief := brief ++ s!"\nRules for this repo, from the communicator:\n{rules.v.getD "None"}\n"
    launchAgent name brief a.model a.effort (wts.head?.map (·.1)) a.full) fun e => do undo wts; throw e
  let (some out, _) := out | do undo wts; Env.err "swarm: launch.sh failed"; return .ok (some out.2)
  let addr := (splitlines (strip out)).getLastD ""
  let now ← Clock.now
  Store.run (Txn.update [Sels.agent name] [] fun db =>
    let db := db.setAgent name fun x => if x.hc.isNone then { x with hc := some addr } else x
    (db.log now (some spawner) "spawn" none (some name), ()))
  if let some tid := a.taskId then
    -- the brief showed `notes`; a held note it missed (none: the task is the new agent's since the reservation) is sent
    let last := notes.foldl (fun x n => max x n.id) 0
    let box := Notes.box tid
    Store.run do
      let c ← Txn.slice [Sels.cursor box]
      Txn.update [Sels.cursor box, Sels.unreadPast box (Msgs.cursorOf c box)] [.msg] fun db =>
        let (db, ns) := Notes.takeHeld name now tid db
        ((ns.filter (·.id > last)).foldl (fun db n =>
          (Msgs.post db now (Msgs.Who.ofText (n.frm.getD "")) (.agent name) s!"[#{d tid}] {n.body.getD ""}" (n.urgent.getD 0 != 0)).1) db, ())
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

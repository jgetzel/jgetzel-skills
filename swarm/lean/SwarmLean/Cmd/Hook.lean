import SwarmLean.Cmd.Locks
import SwarmLean.Lib.Hook
import SwarmLean.Lib.Re
import SwarmLean.Lib.Msgs
import SwarmLean.Lib.Cost
import SwarmLean.Lib.Lifecycle
import SwarmLean.Lib.Workspaces
import SwarmLean.Lib.Machine
import SwarmLean.Sys
import SwarmLean.Db.Sels

/-! `swarm hook <event>` (hook.lua's hook): the hook payload's JSON on stdin, the hook's JSON answer on stdout. -/

namespace SwarmLean.Cmd.Hook
open Args Lean SwarmLean.Hook

/-- The hook events with an output event name (hook.EVENTS); stop has none. -/
def EVENTS : List (String × String) :=
  [("pre-tool", "PreToolUse"), ("post-tool", "PostToolUse"), ("prompt", "UserPromptSubmit"), ("session", "SessionStart")]

/-- The tools that edit a file (hook.EDIT_TOOLS). -/
def EDIT_TOOLS : List String := ["Edit", "Write", "MultiEdit", "NotebookEdit"]

/-- Blocks per reason in one chain of continuations, then the stop goes through and comms is told (hook.STOP_CAP). -/
def STOP_CAP : Nat := 2

/-- `git … push`, with its `-C dir` (log_push). -/
def PUSH : String := "\\bgit\\s+(?:-C\\s+(\\S+)\\s+)?push\\b"
/-- A `cd dir` at the start or after `; & | (` (log_push). -/
def CD : String := "(?:^|[;&|(]\\s*)cd\\s+([^\\s;&|)]+)"

/-- `swarm hook -h`. -/
def helpHook : String :=
  "Usage: swarm hook [-h] {pre-tool,post-tool,prompt,stop,stop-failure,session}\n\nArguments:\n   {pre-tool,post-tool,prompt,stop,stop-failure,session}\n\nOptions:\n   -h, --help            Show this help message and exit."

/-- The `hook` parser. -/
def hookSpec : Spec :=
  .mk "hook" helpHook [{ name := "event", choices := ["pre-tool", "post-tool", "prompt", "stop", "stop-failure", "session"] }] [] [] [] none

/-- A payload field that is a string. -/
def str? (j : Json) (k : String) : Option String :=
  match j.getObjVal? k with | .ok (.str s) => some s | _ => none

/-- Lua's `tostring(x or "")` of a payload field. -/
def tostr (j : Json) (k : String) : String :=
  match j.getObjVal? k with
  | .ok (.str s) => s
  | .ok (.num n) => toString n
  | .ok (.bool b) => toString b
  | _ => ""

/-- A payload field that Lua reads as true: present, not null, not false. -/
def truthy (j : Json) (k : String) : Bool :=
  match j.getObjVal? k with | .ok .null | .ok (.bool false) | .error _ => false | _ => true

variable {m : Type → Type} [Monad m] [MonadExceptOf Exit m] [Store m] [Clock m] [Env m] [Fs m] [Proc m] [Git m] [Sys m]

/-- The pre-tool Bash note when the command is heavy here (cost.predict) and memory is short: information only,
never a deny. -/
def costNote (cmd cwd : String) : m (Option String) := do
  let some pr ← Cost.predict cmd (some cwd) | return none
  let some (avail, total, psi) ← Machine.mem | return none
  if !(pr.peak_kb * 2 > avail || Machine.pressureHigh avail total psi) then return none
  let mins := max 1 (fdiv (pr.wall_s + 30) 60)
  return some s!"`{pr.key}` took ~{fixed (Float.ofInt pr.peak_kb / 1048576) 1}G and {mins} min the last {pr.n} time{if pr.n == 1 then "" else "s"} here; {fixed (Float.ofInt avail / 1048576) 1}G is available now.\n{← Machine.note}"

-- ---------- the hook ----------

/-- Prints the hook's JSON answer. -/
def emit (event : String) (ctx deny : Option String) : m Unit := Env.out (emitText event ctx deny)

/-- `name` edits in worktree `top`: recorded as its `wt`; when another live agent's is `top` too, in any swarm (a
worktree is a repo's), both are told once (a `shared-tree` event per agent and tree), and the context for `name`. -/
def sharedTxn (name top : String) (t : Int) : Txn (Option String) := do
  let d ← Txn.slice [Sels.agent name, { table := .agent, cond := .and (.eq "wt" (.text top)) (.null "ended"), inScope := false }]
  let db := d.setAgent name ({ · with wt := some top })
  let some o := db.agents.find? fun a => a.wt == some top && a.name != name && a.ended.isNone
    | Txn.exec (slicePlan d db); return none
  let e ← Txn.slice [Sels.lastEv name "shared-tree" (.eq "path" (.text top))]
  if !e.events.isEmpty then Txn.exec (slicePlan d db); return none
  let tk ← Txn.slice [{ table := .task, cond := .oneOf "owner" [.text name, .text o.name] }] [.msg]
  let d := { d with tasks := tk.tasks, msgNext := tk.msgNext }
  let db := (d.setAgent name ({ · with wt := some top })).log t (some name) "shared-tree" (some top) (some o.name)
  let (db, _) := Msgs.post db t "swarm" o.name s!"{name} also edits in {top} ({Locks.taskOf db name}). Two agents' uncommitted edits in one tree mix and can't be told apart; make your own worktree." false (some "notice")
  Txn.exec (slicePlan d db)
  return some s!"{top} is also {o.name}'s worktree ({Locks.taskOf db o.name}). Two agents' uncommitted edits in one tree mix and can't be told apart. Make your own: `git worktree add …`."

/-- The pre-tool hook: a cold wake, a base checkout, a heavy command, an edit to a locked path or a shared tree. -/
def preTool (name cwd : String) (tool : Option String) (ti : Json) (here : Option String) : m Unit := do
  let t ← Clock.now
  match tool with
  | some "SendMessage" =>
    let to := match (tostr ti "to").splitOn " [" with | x :: _ => x | [] => ""
    let tgt ← Store.view [Sels.agent to] fun db => db.agents.find? fun a => a.name == to && a.ended.isNone
    let some tgt := tgt | return
    if (String.ofList ((tostr ti "message").toList.dropWhile isSpace)).startsWith "[urgent]" then return
    let (some why, _) ← Agents.coldReason [] tgt t | return
    Store.run (Txn.exec [logStmt t (some name) "deny-cold" (some tgt.name) (some (cut why 120))])
    emit "PreToolUse" none (some (why ++ s!" Use `swarm post {tgt.name} …`: it reads the message when it next wakes. If it truly can't wait, resend starting with `[urgent]`."))
  | some "Bash" =>
    let cmd := tostr ti "command"
    -- the reads only for a checkout: the agent's worktrees and the tasks' bases
    let co := (Re.search Workspaces.CHECKOUT cmd).toOption.join.isSome
    let wdb ← if co then Store.view [Sels.workspaces name, { table := .task, cond := .notNull "base" }] id
      else pure {}
    if let some base ← Workspaces.baseCheckout wdb name cmd (some cwd) then
      Store.run (Txn.exec [logStmt t (some name) "deny-base" (some base) (some (cut cmd 120))])
      emit "PreToolUse" none (some s!"Don't check out {base} in your worktree: a base checked out here blocks `git push . HEAD:{base}` for everyone. Land by a fast-forward of it from your branch (`git push . HEAD:{base}`), or a PR for a remote base.")
      return
    if let some note ← costNote cmd cwd then emit "PreToolUse" (some note) none
  | some tl =>
    if !EDIT_TOOLS.contains tl then return
    let fp := match str? ti "file_path" with | some f => if f == "" then str? ti "notebook_path" else some f | none => str? ti "notebook_path"
    -- the file's own repo: a file of another repo is checked against that repo's locks
    let some (top, p) ← Cmd.Locks.repoRel (fp.getD "") (some cwd) | return
    let lk ← Store.run (Locks.holderTxn name p t)
    if let some lk := lk then
      let who := lk.agent.getD ""
      Store.run (Txn.exec [logStmt t (some name) "deny-lock" (some p.rel) (some who)])
      let why := match lk.reason with | some r => if r != "" then s!" ({r})" else "" | none => ""
      emit "PreToolUse" none (some s!"{p.rel} is locked by {who} since {← Clock.hhmm (lk.since.getD 0)}{why}. Ask it with `swarm post {who} ...`.")
      return
    -- a file of another repo (one the task builds on) is not this agent's worktree: lifecycle would judge it by this
    -- repo's bases and keep the agent forever
    let here ← Workspaces.main none
    if here.isSome && some p.repo != here then return
    let shared ← Store.run (sharedTxn name top t)
    if let some ctx := shared then emit "PreToolUse" (some ctx) none
  | none => return

/-- Logs a `git push` with the branch and subject of the tree it ran in (hook.log_push). -/
def logPush (name cwd cmd : String) : m Unit := do
  let some mt := (Re.search PUSH cmd).toOption.join | return
  let cds := ((Re.findall CD (String.ofList (cmd.toList.take mt.s))).toOption.getD []).map (·.headD "")
  let dir ← match mt.group 1 <|> cds.getLast? with
    | some d =>
      let d := String.ofList ((d.toList.dropWhile (fun c => c == '\'' || c == '"')).reverse.dropWhile (fun c => c == '\'' || c == '"')).reverse
      let d ← if d.startsWith "~" then do
          let home := (← Env.var "HOME").getD "~"
          pure (home ++ (d.drop 1).toString)
        else pure d
      pure (Cmd.Locks.join cwd d)
    | none => pure cwd
  let enc (v : Option String) : String := (v.map fun x => jstr (strip x)).getD "null"
  let branch ← Git.git ["rev-parse", "--abbrev-ref", "HEAD"] (some dir)
  let subject ← Git.git ["log", "-1", "--format=%s"] (some dir)
  let t ← Clock.now
  Store.run (Txn.exec [logStmt t (some name) "push" (some s!"\{\"branch\": {enc branch}, \"subject\": {enc subject}}") (some (cut cmd 120))])

/-- The communicator's name: meta comms when set and nonempty, else $SWARM_COMMS (agents.comms_name). -/
def commsName (db : Db) (envComms : Option String) : Option String :=
  match db.getMeta "comms" with
  | some { v := some v, .. } => if v != "" then some v else envComms
  | _ => envComms

/-- The stop hook's count of blocks for reasons `key` since the chain of continuations began (a stop not continuing
one begins a chain: `stop-chain`): under `STOP_CAP` a `stop-block` event and false, else the stop goes through, the
communicator told, and true. -/
def capTxn (name key : String) (active : Bool) (envComms : Option String) (t : Int) : Txn Bool := do
  let n ← if active then do
      let c ← Txn.slice [Sels.lastEv name "stop-chain"]
      let since := (c.events.map (·.id)).foldl max 0
      let after : Cond := .and (Sels.evOf name "stop-block") (.and (.eq "data" (.text key)) (.gt "id" (.int since)))
      let b ← Txn.slice [{ table := .event, cond := after }]
      pure b.events.length
    else do Txn.exec [logStmt t (some name) "stop-chain" none none]; pure 0
  if n < STOP_CAP then
    Txn.exec [logStmt t (some name) "stop-block" none (some key)]
    return false
  let d ← Txn.slice [Sels.metas ["comms"]] [.msg]
  let db := d.log t (some name) "stop-cap" none (some key)
  let (db, _) := Msgs.post db t "swarm" ((commsName db envComms).getD "")
    s!"{name} stopped though not endable ({key}); the stop hook let it go after {STOP_CAP} blocks." false (some "notice")
  Txn.exec (slicePlan d db)
  return true

/-- The Stop hook's verdict: none lets the stop through, else why it continues (hook.stop_block). -/
def stopBlock (name : String) (p : Json) : m (Option String) := do
  let envComms ← env "SWARM_COMMS"
  let (isC, row) ← Store.view [Sels.metas ["comms"], Sels.agent name] fun db =>
    (Agents.isComms db envComms (some name), db.agents.find? fun a => a.name == name && a.ended.isNone)
  if isC then return none
  if ← errorTurn (str? p "transcript_path") then return none
  let some row := row | return none
  let (db, f) ← Lifecycle.readsOf name
  let rs ← Lifecycle.endableReasons db row f
  let bg := match p.getObjVal? "background_tasks" with
    | .ok (.arr ts) => ts.toList.filter fun x =>
        str? x "status" == some "running" && !((Re.search "swarm\\s+wait" (tostr x "command")).toOption.join.isSome)
    | _ => []
  let bg := if rs.any (·.key == "idle-job") then [] else bg
  if !bg.isEmpty then return none
  if rs.any (·.declared) || rs.isEmpty then return none
  let key := ",".intercalate (rs.map (·.key))
  let t ← Clock.now
  let active := truthy p "stop_hook_active"
  let capped ← Store.run (capTxn name key active envComms t)
  if capped then return none
  let head := "You are not endable: " ++ "\n".intercalate (rs.map (·.text))
  return some (head ++ "\n\nEnd this by changing state, not by arguing: (a) finish and land (`swarm task done`); (b) drop: `swarm task release <id>` and commit, ignore or delete what is listed (pushing the branch counts as handing off commits); (c) declare the wait: `swarm task block <id> \"<question>\"` or `swarm stay \"<what>\"`.")

/-- `swarm hook <event>` (hook.hook). -/
def hook (ev : String) : m UInt32 := do
  let input ← Env.stdin
  let some name ← env "SWARM_NAME" | return 0
  let p := match Json.parse input with | .ok j@(.obj _) => j | _ => Json.mkObj []
  let cwd ← match str? p "cwd" with
    | some c => if c != "" then pure c else Env.cwd
    | none => Env.cwd
  let tool := str? p "tool_name"
  let ti := match p.getObjVal? "tool_input" with | .ok o@(.obj _) => o | _ => Json.mkObj []
  let here ← env "HC_TERMINAL_ID"
  let now ← Clock.now
  if let some f ← Store.view (Sels.fence name) fun db => Agents.fence db name here then
    let why ← Agents.fenceText name f
    let at_ := here.getD "-"
    if let some out := EVENTS.lookup ev then
      let fresh ← Store.run do
        let d ← Txn.slice [Sels.lastEv name "fenced" (.and (.eq "path" (.text at_)) (.eq "data" (.text why)))]
        if !d.events.isEmpty then return false
        Txn.exec [logStmt now (some name) "fenced" (some at_) (some why)]
        return true
      if fresh then emit out (some why) none
    return 0
  Store.run (Sels.onAgent name fun db => (Agents.touch db name (some cwd) here now, ()))
  let transcript := str? p "transcript_path"
  if let some tp := transcript then  -- watchd reads the transcript's end (api-error pass)
    Store.run (Txn.update [Sels.metas ["tr:" ++ name]] [] fun db =>
      (if ((db.getMeta ("tr:" ++ name)).bind (·.v)) == some tp then db else db.setMeta ("tr:" ++ name) (some tp), ()))
  match ev with
  | "pre-tool" => preTool name cwd tool ti here
  | "post-tool" =>
    Store.run (Sels.onAgent name fun db => (setStatus db name here now "working", ()))
    if tool == some "Bash" then logPush name cwd (tostr ti "command")
    let ctx ← Msgs.deliver name
    recordCtx name transcript
    if ctx != "" then emit "PostToolUse" (some ctx) none
  | "prompt" =>
    Store.run (Sels.onAgent name fun db => (setStatus db name here now "working", ()))
    let msg ← Msgs.deliver name
    if msg != "" then emit "UserPromptSubmit" (some msg) none
  | "stop" =>
    let k ← ctxFrom transcript
    Store.run (Sels.onAgent name fun db =>
      let db := setStatus db name here now "idle" fun a => match k with | some k => { a with ctx_tokens := some k } | none => a
      (if k.isNone then db.setAgent name ({ · with ctx_tokens := none }) else db, ()))
    if let some why ← stopBlock name p then Env.out ("{\"decision\": \"block\", \"reason\": " ++ jstr why ++ "}")
  | "stop-failure" =>  -- the turn ended on an API error: no Stop hook runs
    let txt := (← errorText transcript).getD (tostr p "error")
    Store.run (Sels.onAgent name fun db =>
      ((setStatus db name here now "idle").log now (some name) "api-error" none (some txt), ()))
  | "session" =>
    let pid ← Machine.claudePid
    Store.run (Sels.onAgent name fun db =>
      ((Agents.touchWith db name none here now false fun a => match pid with | some x => { a with claude_pid := some x } | none => a).1, ()))
    if str? p "source" == some "compact" then
      let k ← postCompact transcript
      Store.run (Sels.onAgent name fun db =>
        let db := (Agents.touchWith db name none here now false fun a =>
          { a with compacted_at := some now, ctx_tokens := k.orElse fun _ => a.ctx_tokens }).1
        (if k.isNone then db.setAgent name ({ · with ctx_tokens := none }) else db, ()))
      Store.run (Txn.exec [logStmt now (some name) "compact" none none])
    else Store.run (Sels.onAgent name fun db => (setStatus db name here now "idle", ()))
  | _ => die s!"unknown hook event {ev}"
  return 0

/-- The group: hook. -/
def group : Group m where
  specs := [("hook", hookSpec)]
  run a := hook ((a.str "event").getD "")

end SwarmLean.Cmd.Hook

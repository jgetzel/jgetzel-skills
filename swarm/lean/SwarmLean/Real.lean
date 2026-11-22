import SwarmLean.World
import SwarmLean.Db.Plan
import SwarmLean.Db.Schema
import Std.Data.HashMap
import Lean.Data.Json

/-! The real world: the instances of the interfaces on IO, and the SQLite store on the Lua CLI's database. -/

namespace SwarmLean
open Sqlite

/-- What the real monad carries: the connection, opened at the first transaction, and the scope, resolved then. -/
structure Ctx where
  conn : IO.Ref (Option Conn)
  scope : IO.Ref (Option Scope)

/-- A context with no connection yet and the scope unresolved. -/
def Ctx.new : IO Ctx := return { conn := ← IO.mkRef none, scope := ← IO.mkRef none }

/-- The real monad: IO with the connection, and an early exit. -/
abbrev App := ExceptT Exit (ReaderT Ctx IO)

/-- The columns a table has now. -/
def tableCols (c : Conn) (t : String) : IO (List String) := do
  let rows ← c.query s!"pragma table_info({t})"
  return rows.toList.filterMap fun r => match r[1]? with | some (Val.text n) => some n | _ => none

/-- The machine's db: $SWARM_DB (tests), else swarm/swarm.db in $XDG_STATE_HOME, else in ~/.local/state. -/
def dbPath : IO String := do
  if let some p ← IO.getEnv "SWARM_DB" then if p ≠ "" then return p
  let st ← match ← IO.getEnv "XDG_STATE_HOME" with
    | some x => if x ≠ "" then pure x else pure (((← IO.getEnv "HOME").getD "") ++ "/.local/state")
    | none => pure (((← IO.getEnv "HOME").getD "") ++ "/.local/state")
  return st ++ "/swarm/swarm.db"

/-- Runs the statements in order. -/
def runStmts (c : Conn) (p : List Stmt) : IO Unit := do
  for st in p do
    for (q, ps) in st.sql do discard <| c.exec q ps

/-- Opens the db as db.connect does: makes its dir, turns on WAL (retrying a first connect that races another), runs
the schema and adds missing columns. -/
def connect : IO Conn := do
  let p ← dbPath
  if let some dir := (p : System.FilePath).parent then if dir.toString ≠ "" then IO.FS.createDirAll dir
  let c ← Conn.open p false
  let mut i := 0
  repeat
    i := i + 1
    try discard <| c.query "pragma journal_mode=wal"; break
    catch e =>
      if i ≥ 500 || !hasSub (toString e) "database is locked" then throw e
      IO.sleep 20
  -- per connection: at sqlite's default (full) every commit fsyncs the WAL while it holds the write lock, and on a busy
  -- disk that took seconds, so the others ran out their busy timeout; a power cut may now lose the last commits
  discard <| c.query "pragma synchronous=normal"
  c.script schema
  -- each migration checked again inside the transaction: another connect may have run it
  let has : IO (String → List String) := do
    let l ← migTables.mapM fun t => do pure (t, ← tableCols c t)
    pure fun t => (l.lookup t).getD []
  let now ← has
  if migs.any (·.needed now) then
    discard <| c.exec "begin immediate"
    try
      for m in migs do
        if m.needed (← has) then runStmts c [m]
      discard <| c.exec "commit"
    catch e => discard (c.exec "rollback"); throw e
  return c

/-- The connection, opened on first use. -/
def theConn : App Conn := do
  let r := (← read).conn
  match ← r.get with
  | some c => pure c
  | none => let c ← connect; r.set (some c); pure c

@[extern "swarm_setenv"] opaque setenvIO (k v : @& String) : IO Unit

/-- The repo of the working directory: its main worktree (the first `git worktree list` names), resolved; `''` outside
one. -/
def repoHere : IO String := do
  let out ← try
      let r ← IO.Process.output { cmd := "git", args := #["worktree", "list", "--porcelain"], env := Git.ENV.toArray.map fun (k, v) => (k, some v) }
      pure (if r.exitCode == 0 then r.stdout else "")
    catch _ => pure ""
  if !out.startsWith "worktree " then return ""
  let p := String.ofList ((out.drop 9).toString.toList.takeWhile (· ≠ '\n'))
  try return (← IO.FS.realPath p).toString catch _ => return p

/-- The first column of each row, as text. -/
def texts (rows : Array (Array Sqlite.Val)) : List String :=
  rows.toList.filterMap fun (r : Array Sqlite.Val) => match r[0]? with | some (Sqlite.Val.text s) => some s | _ => none

/-- The swarms not ended, by name. -/
def liveSwarms (c : Conn) : IO (List String) := return texts (← c.query "select name from swarm where ended is null order by name")

/-- The `swarm` label hc keeps on terminal `h`, if any. -/
def hcSwarmLabel (h : String) : IO (Option String) := do
  try
    let r ← IO.Process.output { cmd := "hc", args := #["get", h] }
    if r.exitCode ≠ 0 then return none
    let j ← IO.ofExcept (Lean.Json.parse r.stdout)
    return ((j.getObjValD "labels").getObjValAs? String "swarm").toOption
  catch _ => return none

/-- The swarm this process acts on (sw-global §2), never from the folder: `$SWARM` (`--swarm` sets it), the swarm of
`$SWARM_NAME`'s agent row, the hc label `swarm=<name>` of `$HC_TERMINAL_ID`, the only live swarm; else why not. -/
def resolveSwarm (c : Conn) : IO (Except String String) := do
  let has (s : String) : IO Bool := return !(← c.query "select 1 from swarm where name=?" [.text s]).isEmpty
  let var (k : String) : IO (Option String) := return (← IO.getEnv k).filter (· ≠ "")
  if let some s ← var "SWARM" then
    return if ← has s then .ok s else .error s!"no swarm '{s}' (`swarm swarms` lists them; `swarm new {s}` makes it)"
  if let some n ← var "SWARM_NAME" then
    if let some s := (texts (← c.query "select swarm from agent where name=? and swarm is not null" [.text n])).head? then
      return .ok s
  if let some h ← var "HC_TERMINAL_ID" then
    if let some s ← hcSwarmLabel h then if ← has s then return .ok s
  match ← liveSwarms c with
  | [s] => return .ok s
  | [] => return .error "no swarm on this machine: `swarm new <name>` makes one (or `swarm join` as <name>-comms)"
  | l => return .error s!"which swarm? Pass --swarm <name> or set $SWARM; live: {", ".intercalate l}"

/-- Acts on swarm `s` from here on, and exports it as `$SWARM` to what this process starts. -/
def useSwarm (s : String) : App Scope := do
  let sc : Scope := { swarm := s, repo := ← repoHere }
  (← read).scope.set (some sc)
  setenvIO "SWARM" s
  return sc

/-- The scope, resolved on first use; a process with no swarm to act on stops here. -/
def theScope : App Scope := do
  match ← (← read).scope.get with
  | some sc => pure sc
  | none =>
    match ← resolveSwarm (← theConn) with
    | .ok s => useSwarm s
    | .error e => IO.eprintln s!"swarm: {e}"; throw (Exit.mk 1)

/-- All rows of a row type's table, in key order (asked of SQLite so that `decodeRows` only checks it). -/
def loadRows [Row α] (c : Conn) : IO (List α) := do
  let cols := Row.cols α
  let rows ← c.query s!"select {", ".intercalate cols} from {Row.table α} order by {", ".intercalate (cols.take (Row.nkey α))}"
  IO.ofExcept (decodeRows rows.toList)

/-- The next id of an AUTOINCREMENT table: one past the larger of its sqlite_sequence entry and its largest id (an
old db with no AUTOINCREMENT table has no sqlite_sequence: 0). -/
def nextId (c : Conn) (t : String) : IO Nat := do
  let has ← c.query "select 1 from sqlite_master where name='sqlite_sequence'" []
  let seq ← if has.isEmpty then pure #[] else c.query "select seq from sqlite_sequence where name=?" [.text t]
  let mx ← c.query s!"select coalesce(max(id),0) from {t}"
  let get (rows : Array (Array Val)) : Nat := match rows[0]?.bind (·[0]?) with | some (Val.int i) => i.toNat | _ => 0
  return max (get seq) (get mx) + 1

/-- The rows of a row type's table that `cond` (a where clause over `ps`) selects, in key order. -/
def loadWhere [Row α] (c : Conn) (cond : String) (ps : List Val) : IO (List α) := do
  let cols := Row.cols α
  let rows ← c.query s!"select {", ".intercalate cols} from {Row.table α} where {cond} order by {", ".intercalate (cols.take (Row.nkey α))}" ps
  IO.ofExcept (decodeRows rows.toList)

/-- The meta rows swarm `s` sees that `cond` selects: the machine's keys and those of meta scope `ms` (the swarm's own
by default), and `comms` from its swarm row. -/
def loadMetasWhere (c : Conn) (s : String) (cond : Cond) (ms : String := s) : IO (List Meta) := do
  let ks := ", ".intercalate (machineKeys.map fun k => s!"'{k}'")
  let (w, ps) := cond.sql
  let ms : List Meta ← loadWhere c s!"scope = case when k in ({ks}) then '' else ? end and ({w})" (.text ms :: ps)
  let cm ← c.query "select comms from swarm where name=? and comms is not null" [.text s]
  let cms : List Meta := match (cm[0]? : Option (Array Sqlite.Val)).bind (·[0]?) with
    | some (Sqlite.Val.text v) => [{ k := "comms", v := some v }]
    | _ => []
  return sortRows (cms.filter (fun m => cond.holds (Row.cell m)) ++ ms.filter (·.k != "comms"))

/-- A statement on the machine's db: rows of the scoped tables get the scope's swarm or repo, keys the scope
column (a lock carries its own repo, and so does a workspace), and meta `comms` is the swarm row's. A new agent row
replaces one of that name in another swarm: the agent moves (names are the machine's). -/
def scopeStmt (sc : Scope) : Stmt → Stmt
  | .ins "event" cs vs => .ins "event" (cs ++ ["swarm", "repo"]) (vs ++ [.text sc.swarm, .text sc.repo])
  | .ins "meta" cs vs => match vs with
    | [.text "comms", v] => .upd "swarm" ["name"] [.text sc.swarm] ["comms"] [v]
    | .text k :: _ => .ins "meta" (cs ++ ["scope"]) (vs ++ [.text (metaScope sc.metaName k)])
    | _ => .ins "meta" cs vs
  | .upd "meta" ks k cs vs => match k with
    | [.text "comms"] => .upd "swarm" ["name"] [.text sc.swarm] ["comms"] vs
    | [.text kk] => .upd "meta" (ks ++ ["scope"]) (k ++ [.text (metaScope sc.metaName kk)]) cs vs
    | _ => .upd "meta" ks k cs vs
  | .del "meta" ks k => match k with
    | [.text "comms"] => .upd "swarm" ["name"] [.text sc.swarm] ["comms"] [.null]
    | [.text kk] => .del "meta" (ks ++ ["scope"]) (k ++ [.text (metaScope sc.metaName kk)])
    | _ => .del "meta" ks k
  | .ins t cs vs => if ["ci"].contains t then .ins t (cs ++ ["repo"]) (vs ++ [.text sc.repo]) else .ins t cs vs
  | .upd t ks k cs vs => if ["ci"].contains t then .upd t (ks ++ ["repo"]) (k ++ [.text sc.repo]) cs vs
    else .upd t ks k cs vs
  | .del t ks k => if ["ci"].contains t then .del t (ks ++ ["repo"]) (k ++ [.text sc.repo]) else .del t ks k
  | st => st

/-- `scopeStmt`, an agent's insert after a delete of its name. -/
def scopeStmts (sc : Scope) : Stmt → List Stmt
  | .ins "agent" cs vs => [.del "agent" ["name"] (vs.take 1), .ins "agent" (cs ++ ["swarm"]) (vs ++ [.text sc.swarm])]
  | st => [scopeStmt sc st]

/-- An event a scope with every swarm in view inserts belongs to its agent's swarm (none: no swarm's). -/
def agentSwarm (c : Conn) (sc : Scope) : Stmt → IO Stmt
  | .ins "event" cs vs => do
    if !sc.every then return .ins "event" cs vs
    let sw ← match (cs.zip vs).lookup "agent" with
      | some (.text a) => pure ((texts (← c.query "select swarm from agent where name=? and swarm is not null" [.text a])).headD "")
      | _ => pure ""
    return .ins "event" cs ((cs.zip vs).map fun (k, v) => if k == "swarm" then .text sw else v)
  | st => return st

/-- `act` between `begin` and COMMIT; any error rolls back. -/
def inTxn (c : Conn) (begin : String) (act : IO α) : IO α := do
  discard <| c.exec begin
  try
    let a ← act
    discard <| c.exec "commit"
    return a
  catch e =>
    try discard <| c.exec "rollback" catch _ => pure ()
    throw e

/-- The condition a select of table `t` is scoped by: the scope's swarm for agents (none when
`every`) and events, its repo for CI runs, its repo and its agents for worktrees (meta is scoped by `loadMetasWhere`). A
lock row carries its repo, so a select of locks names it. -/
def scopeCond (sc : Scope) : Table → Option (String × List Val)
  | .agent => if sc.every then none else some ("swarm=?", [.text sc.swarm])
  | .event =>
    if sc.every && sc.repo == "" then some ("(swarm='' or kind in ('job-start', 'job-end'))", [])
    else if sc.every then some ("repo=?", [.text sc.repo])
    else if sc.swarm == "" then some ("swarm='' and repo=?", [.text sc.repo])
    else some ("swarm=?", [.text sc.swarm])
  | .ci => some ("repo=?", [.text sc.repo])
  | .workspace =>
    if sc.every then some ("(repo=? or agent in (select name from agent))", [.text sc.repo])
    else some ("(repo=? or agent in (select name from agent where swarm=?))", [.text sc.repo, .text sc.swarm])
  | _ => none

/-- The rows of a row type's table that select `s` picks, in the scope `sc`, in key order: one indexed select. -/
def selRows [Row α] (c : Conn) (sc : Scope) (s : Sel) : IO (List α) := do
  let (w, ps) := s.cond.sql
  let (w, ps) := match if s.inScope then scopeCond sc s.table else none with
    | some (sw, sps) => (s!"{sw} and ({w})", sps ++ ps)
    | none => (w, ps)
  let ks := (Row.cols α).take (Row.nkey α)
  match s.last with
  | none => loadWhere c w ps
  | some n =>
    let rows ← c.query s!"select {", ".intercalate (Row.cols α)} from {Row.table α} where {w} order by {", ".intercalate (ks.map (· ++ " desc"))} limit {n}" ps
    IO.ofExcept (decodeRows rows.toList)

/-- Rows in key order with one of each key. -/
def dedupKeys [Row α] : List α → List α
  | a :: b :: l => if Row.key a == Row.key b then dedupKeys (a :: l) else a :: dedupKeys (b :: l)
  | l => l

/-- The rows of table `t` that any of the selects `ss` of it picks, in scope `sc`. -/
def unionRows [Row α] (c : Conn) (sc : Scope) (t : Table) (ss : List Sel) : IO (List α) := do
  match ss.filter (·.table == t) with
  | [] => return []
  | [s] => selRows c sc s
  | l => return dedupKeys (sortRows (← l.flatMapM (selRows c sc)))

/-- The meta rows scope `sc` sees that select `sel` picks (`loadMetasWhere`, filtered). -/
def selMetas (c : Conn) (sc : Scope) (sel : Sel) : IO (List Meta) :=
  return sel.pick (← loadMetasWhere c sc.swarm sel.cond sc.metaName)

/-- The slice of the db the selects `ss` pick in scope `sc`, with the next ids of `next` (`Db.slice` of the model). -/
def readSlice (c : Conn) (sc : Scope) (ss : List Sel) (next : List Table) : IO Db := do
  let metas ← match ss.filter (·.table == .«meta») with
    | [] => pure []
    | l => do pure (dedupKeys (sortRows (← l.flatMapM (selMetas c sc))))
  return {
    agents := ← unionRows c sc .agent ss, msgs := ← unionRows c sc .msg ss, cursors := ← unionRows c sc .cursor ss,
    tasks := ← unionRows c sc .task ss, locks := ← unionRows c sc .lock ss, conflicts := ← unionRows c sc .conflict ss,
    pairkeys := ← unionRows c sc .pairkey ss, metas, events := ← unionRows c sc .event ss,
    workspaces := ← unionRows c sc .workspace ss, cis := ← unionRows c sc .ci ss,
    taskNext := ← if next.contains .task then nextId c "task" else pure 0
    msgNext := ← if next.contains .msg then nextId c "msg" else pure 0
    eventNext := ← if next.contains .event then nextId c "event" else pure 0
    swarm := sc.swarm }

/-- Runs a transaction's program on the connection, in scope `sc`. With `writes` false (a read transaction) it stops
at the first write or guarded update, with none: the caller runs it again under BEGIN IMMEDIATE. -/
def runTxnOn (c : Conn) (sc : Scope) (writes : Bool) : Txn α → IO (Option α)
  | .done a => return some a
  | .read ss n k => do runTxnOn c sc writes (k (← readSlice c sc ss n))
  | .write p k => do
    if p.isEmpty then return ← runTxnOn c sc writes k
    if !writes then return none
    runStmts c (← (p.flatMap (scopeStmts sc)).mapM (agentSwarm c sc))
    runTxnOn c sc writes k
  | .guard s cond k => do
    if !writes then return none
    let (w, cps) := cond.sql
    let mut n := 0
    for (q, ps) in (scopeStmt sc s).sql do
      n := n + (← c.exec (q ++ s!" and ({w})") (ps ++ cps))
    runTxnOn c sc writes (k (n > 0))

/-- The statement store's transaction (sw-global §3): the reads and the decision in a read transaction (BEGIN, no
write lock), which ends there when it writes nothing; one that writes runs again, reads, decision and plan, in one BEGIN
IMMEDIATE (the decision is pure, so the second run is the transaction). Any error rolls back. -/
def sqliteRun (c : Conn) (sc : Scope) (t : Txn α) : IO α := do
  if let some a ← inTxn c "begin" (runTxnOn c sc false t) then return a
  match ← inTxn c "begin immediate" (runTxnOn c sc true t) with
  | some a => return a
  | none => throw (IO.userError "swarm: a transaction stopped short under BEGIN IMMEDIATE")

instance : Store App where
  run t := do sqliteRun (← theConn) (← theScope) t
  view ss f := do
    let c ← theConn
    let sc ← theScope
    return f (← inTxn c "begin" (readSlice c sc ss []))

instance : Scoped App where
  within sc x := ExceptT.mk fun ctx => do
    let old ← ctx.scope.get
    let oldSw ← IO.getEnv "SWARM"
    let oldDir ← IO.currentDir
    ctx.scope.set (some sc)
    if sc.swarm != "" then setenvIO "SWARM" sc.swarm
    if sc.repo != "" then try IO.Process.setCurrentDir sc.repo catch _ => pure ()
    try x.run ctx
    finally
      ctx.scope.set old
      setenvIO "SWARM" (oldSw.getD "")
      try IO.Process.setCurrentDir oldDir catch _ => pure ()

instance : Guard App where
  guard x := ExceptT.mk fun ctx => do
    try
      match ← x.run ctx with
      | .ok a => pure (.ok (.ok a))
      | .error e => pure (.ok (.error s!"exit {e.code}"))
    catch e => pure (.ok (.error (toString e)))

instance : Clock App where
  now := return (← Sqlite.now).toNat
  hhmm t := Sqlite.hhmm (Int64.ofInt t)

instance : Env App where
  var k := IO.getEnv k
  out s := do let h ← IO.getStdout; h.putStrLn s
  err s := do let h ← IO.getStderr; h.putStrLn s; h.flush
  stdin := do (← IO.getStdin).readToEnd
  cwd := return (← IO.currentDir).toString

/-- A file's text, or none; `-` reads stdin. -/
def readIO (p : String) : IO (Option String) := do
  if p == "-" then return some (← (← IO.getStdin).readToEnd)
  try return some (← IO.FS.readFile p) catch _ => return none

/-- A directory's entry names, or none. -/
def listIO (p : String) : IO (Option (List String)) := do
  try return some ((← System.FilePath.readDir p).toList.map (·.fileName)) catch _ => return none

/-- Writes a file; false when it can't. -/
def writeIO (p s : String) : IO Bool := do
  try IO.FS.writeFile p s; return true catch _ => return false

/-- Runs a command to its end, capturing its output; none if it can't start. -/
def outputIO (argv : List String) (cwd : Option String) (env : List (String × String)) : IO (Option ProcOut) := do
  match argv with
  | [] => return none
  | cmd :: args =>
    try
      let o ← IO.Process.output { cmd, args := args.toArray, cwd := cwd.map (·), env := env.toArray.map fun (k, v) => (k, some v) }
      return some { code := o.exitCode, stdout := o.stdout, stderr := o.stderr }
    catch _ => return none

/-- execvp, or why it failed. -/
def execIO (argv : List String) : IO String := do
  (← IO.getStdout).flush
  try Sqlite.execvp (argv.headD "") argv.toArray; return "exec returned"
  catch e => return toString e

/-- The first directory above this binary holding the launcher `swarm` and `lean/lakefile.lean` (swarm/ in the repo). -/
def launcherDirIO : IO (Option String) := do
  let mut dir := (← IO.appPath).parent
  while dir.isSome do
    let d := dir.get!
    if (← (d / "lean" / "lakefile.lean").pathExists) && (← (d / "swarm").pathExists) then
      return some d.toString
    dir := if d.parent == some d then none else d.parent
  return none

instance : Fs App where
  read p := readIO p
  list p := listIO p
  write p s := writeIO p s

instance : Proc App where
  output argv cwd env := outputIO argv cwd env
  exec argv := execIO argv
  launcherDir := launcherDirIO

instance : Git App where
  git args cwd := do
    match ← outputIO ("git" :: args) cwd Git.ENV with
    | some o => return if o.code == 0 then some o.stdout else none
    | none => return none

end SwarmLean

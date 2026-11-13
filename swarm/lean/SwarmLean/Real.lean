import SwarmLean.World
import SwarmLean.Db.Plan
import Std.Data.HashMap

/-! The real world: the instances of the interfaces on IO, and the SQLite store on the Lua CLI's database. -/

namespace SwarmLean
open Sqlite

/-- db.lua's SCHEMA, as is. -/
def schema : String := "
create table if not exists agent(name text primary key, hc text, model text, cwd text, status text,
  last_active int, ctx_tokens int default 0, compacted_at int default 0, started int, ended int, snap text,
  waiter int, wt text);
create table if not exists msg(id integer primary key autoincrement, ts int, frm text, dest text,
  body text, urgent int default 0, kind text);
create table if not exists cursor(agent text primary key, last_msg_id int default 0);
create table if not exists task(id integer primary key autoincrement, title text, body text,
  state text default 'open', owner text, lease_until int, created_by text, evidence text, deps text, model text, question text,
  effort text);
create table if not exists lock(path text primary key, agent text, reason text, since int, lease_until int, seen int default 0);
create table if not exists conflict(a text, b text, path text, since int, primary key(a,b,path));
create table if not exists pairkey(a text, b text, key text, primary key(a,b));
create table if not exists meta(k text primary key, v text);
create table if not exists event(id integer primary key autoincrement, ts int, agent text, kind text,
  path text, data text);
create table if not exists workspace(path text, branch text, base text, agent text, ro int default 0, primary key(path, agent));
create table if not exists ci(id integer primary key, sha text, status text, conclusion text, url text,
  created text, updated text, failed text);
"

/-- What the real monad carries: the db path and the connection, opened at the first transaction. -/
structure Ctx where
  conn : IO.Ref (Option Conn)

/-- The real monad: IO with the connection, and an early exit. -/
abbrev App := ExceptT Exit (ReaderT Ctx IO)

/-- The columns a table has now. -/
def tableCols (c : Conn) (t : String) : IO (List String) := do
  let rows ← c.query s!"pragma table_info({t})"
  return rows.toList.filterMap fun r => match r[1]? with | some (Val.text n) => some n | _ => none

/-- The db file (db.dbpath): $SWARM_DB, else swarm/swarm.db in the repo's git common dir. -/
def dbPath : IO String := do
  if let some p ← IO.getEnv "SWARM_DB" then if p ≠ "" then return p
  let r ← IO.Process.output { cmd := "git", args := #["rev-parse", "--path-format=absolute", "--git-common-dir"] }
  let d := strip r.stdout
  if r.exitCode ≠ 0 || d.isEmpty then throw <| IO.userError "not in a git repo and SWARM_DB is unset"
  return d ++ "/swarm/swarm.db"

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

/-- All rows of a row type's table, in key order. -/
def loadRows [Row α] (c : Conn) : IO (List α) := do
  let rows ← c.query s!"select {", ".intercalate (Row.cols α)} from {Row.table α}"
  IO.ofExcept (decodeRows rows.toList)

/-- The next id of an AUTOINCREMENT table: one past the larger of its sqlite_sequence entry and its largest id (an
old db with no AUTOINCREMENT table has no sqlite_sequence: 0). -/
def nextId (c : Conn) (t : String) : IO Nat := do
  let has ← c.query "select 1 from sqlite_master where name='sqlite_sequence'" []
  let seq ← if has.isEmpty then pure #[] else c.query "select seq from sqlite_sequence where name=?" [.text t]
  let mx ← c.query s!"select coalesce(max(id),0) from {t}"
  let get (rows : Array (Array Val)) : Nat := match rows[0]?.bind (·[0]?) with | some (Val.int i) => i.toNat | _ => 0
  return max (get seq) (get mx) + 1

/-- Loads the tables `ts` into a db (the others empty) with the next ids. -/
def loadDb (c : Conn) (ts : List Table) : IO Db := do
  let has (t : Table) := ts.contains t
  return {
    agents := ← if has .agent then loadRows c else pure []
    msgs := ← if has .msg then loadRows c else pure []
    cursors := ← if has .cursor then loadRows c else pure []
    tasks := ← if has .task then loadRows c else pure []
    locks := ← if has .lock then loadRows c else pure []
    conflicts := ← if has .conflict then loadRows c else pure []
    pairkeys := ← if has .pairkey then loadRows c else pure []
    metas := ← if has .«meta» then loadRows c else pure []
    events := ← if has .event then loadRows c else pure []
    workspaces := ← if has .workspace then loadRows c else pure []
    cis := ← if has .ci then loadRows c else pure []
    taskNext := ← nextId c "task", msgNext := ← nextId c "msg", eventNext := ← nextId c "event" }

/-- Writes every table of `new` over what `old` loaded (`dbPlan`). -/
def storeDb (c : Conn) (old new : Db) : IO Unit := runStmts c (dbPlan old new)

/-- The real store's transaction: BEGIN IMMEDIATE, load the tables `ts`, apply `f`, write back what changed, COMMIT;
any error rolls back. -/
def sqliteTxn (c : Conn) (ts : List Table) (f : Db → Db × α) : IO α := do
  discard <| c.exec "begin immediate"
  try
    let db ← loadDb c ts
    let (db', a) := f db
    if db' ≠ db then storeDb c db db'
    discard <| c.exec "commit"
    return a
  catch e =>
    try discard <| c.exec "rollback" catch _ => pure ()
    throw e

instance : Store App where
  txn ts f := do sqliteTxn (← theConn) ts f

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
    match ← outputIO ("git" :: args) cwd [] with
    | some o => return if o.code == 0 then some o.stdout else none
    | none => return none

end SwarmLean

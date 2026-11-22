import Tests.Cli.Fixture
import SwarmLean.Db.TaskTxn

/-! sqlite_spec.lua: the store assumption (Assumptions.lean's `Atomic`, and the sqlite behaviour its tags name) against
real sqlite through the code's own store: `connect` (WAL, a 10 s busy handler) and `sqliteRun` (`Store.run`: reads
and the decision in a read transaction; one that writes run again, reads, decision and plan, under BEGIN IMMEDIATE),
many processes at once. Each case carries the name a tag gives. The other
processes are this binary's `--sqlite <role> …` (`worker`), each on its own connection to $SWARM_DB. Counters and
accounts are meta rows. -/

namespace SwarmLean.Tests.Spec.Sqlite
open SwarmLean SwarmLean.Tests.Cli
open SwarmLean.Sqlite (Conn Val)
open Lean (Json toJson)

/-- Counter workers, and the transactions each runs. -/
def N : Nat := 6
-- shortcut: sized so the whole stress ends well within busy_timeout (10 s) under the suite's parallel load; at 150 (the
-- Lua's) four at once ran past it, the busy handler starving one writer from its first transaction
def K : Nat := 60

/-- Meta `k` as a number (0 when missing). -/
def getI (db : Db) (k : String) : Int := (((db.metas.find? (·.k == k)).bind (·.v)).bind String.toInt?).getD 0

/-- Sets meta `k` to `v`. -/
def setI (db : Db) (k : String) (v : Int) : Db :=
  if db.metas.any (·.k == k) then
    { db with metas := db.metas.map fun m => if m.k == k then { m with v := some (toString v) } else m }
  else { db with metas := db.metas ++ [{ k, v := some (toString v) }] }

/-- The first cell of the first row, as a number. -/
def int (c : Conn) (sql : String) : IO Int := do
  let v : Option Val := (← c.query sql)[0]?.bind (·[0]?)
  match v with
  | some (.int i) => pure i
  | some (.text s) => pure (s.toInt?.getD 0)
  | _ => fail s!"{sql}: no number"

/-- A step of the meta rows, as a transaction of the store. -/
def onMetas (f : Db → Db × α) : Txn α := Txn.update [{ table := .«meta» }] [] f

/-- The machine's scope with no swarm: every meta key is scope `''`, as the raw statements here write them. -/
def sc0 : Scope := { swarm := "t", repo := "" }

def sumSql : String := "select coalesce(sum(cast(v as integer)),0)*100 + count(*) from meta where k like 'acct.%'"

/-- Prints a line and flushes it: the parent waits for it. -/
def signal : IO Unit := do let o ← IO.getStdout; o.putStrLn "x"; o.flush

/-- A worker process's role. tx: K transactions adding one to meta tx, each logging the value it read (an event of kind
seen); `tx auto` adds one to meta auto outside a transaction after each. auto: K writes outside a transaction adding
one to meta auto. move <i>: K transactions moving 1 between two of eight accounts. sum: 4K reads of the accounts' total.
hold: holds the write lock 1 s (BEGIN IMMEDIATE, auto = -1). readhold: holds a read transaction 1 s. victim: BEGIN
IMMEDIATE, a write, then waits to be killed. -/
def worker (role : String) (args : List String) : IO UInt32 := do
  let t0 ← IO.monoMsNow
  tryCatch (go role args) fun e => do
    IO.eprintln s!"{role} {args}: {e} after {(← IO.monoMsNow) - t0} ms"; return 1
where go (role : String) (args : List String) : IO UInt32 := do
  let c ← connect
  match role, args with
  | "tx", rest =>
    let both := rest == ["auto"]
    for _ in [0:K] do
      sqliteRun c sc0 <| onMetas fun db => let v := getI db "tx"; ((setI db "tx" (v + 1)).log 0 none "seen" (some (toString v)) none, ())
      if both then discard <| c.exec "update meta set v=cast(v as integer)+1 where k='auto'"
  | "auto", [] =>
    for _ in [0:K] do discard <| c.exec "update meta set v=cast(v as integer)+1 where k='auto'"
  | "move", [i] =>
    let mut g := mkStdGen i.toNat!
    for _ in [0:K] do
      let (a, g1) := randNat g 1 8
      let (b, g2) := randNat g1 1 8
      g := g2
      sqliteRun c sc0 <| onMetas fun db =>
        let db := setI db s!"acct.{a}" (getI db s!"acct.{a}" - 1)
        (setI db s!"acct.{b}" (getI db s!"acct.{b}" + 1), ())
  | "sum", [] =>
    for _ in [0:4 * K] do
      let s ← int c sumSql
      if s != 80008 then fail s!"sqlite_read, sqlite_commit: a read saw part of a transaction ({s})"
  | "hold", [] =>
    discard <| c.exec "begin immediate"; discard <| c.exec "update meta set v='-1' where k='auto'"
    signal; IO.sleep 1000
    discard <| c.exec "commit"
  | "readhold", [] =>
    discard <| c.exec "begin"; discard <| c.query "select count(*) from meta"
    signal; IO.sleep 1000
    discard <| c.exec "commit"
  | "victim", [] =>
    discard <| c.exec "begin immediate"; discard <| c.exec "insert into meta(k, v) values('seen.-7','-7')"
    signal; IO.sleep 30000
  | _, _ => IO.eprintln s!"no sqlite role {role} {args}"; return 2
  return 0

abbrev W := IO.Process.Child ⟨.null, .piped, .piped⟩

/-- Starts a worker on db `t.db`. -/
def spawnW (t : T) (args : List String) : IO W := do
  IO.Process.spawn { cmd := ← selfBin, args := #["--sqlite"] ++ args.toArray, env := #[("SWARM_DB", some t.db)],
                     stdin := .null, stdout := .piped, stderr := .piped }

/-- Waits for the workers; fails with `msg` and their errors if any failed. -/
def waitAll (ws : Array W) (msg : String) : IO Unit := do
  let mut errs := #[]
  for w in ws do
    let e ← w.stderr.readToEnd
    if (← w.wait) != 0 then errs := errs.push e
  if !errs.isEmpty then fail s!"{msg}: {errs.size} failed\n{"".intercalate errs.toList}"

/-- Runs `roles` (each `n` workers) at once. -/
def stress (t : T) (roles : List (Nat × List String)) (msg : String) : IO Unit := do
  let mut ws := #[]
  for (n, r) in roles do
    for i in [0:n] do ws := ws.push (← spawnW t (if r == ["move"] then r ++ [toString (i + 1)] else r))
  waitAll ws msg

/-- The db with meta tx and auto at 0 and eight accounts of 100; a connection to it. -/
def setup (t : T) : IO Conn := do
  Shim.setenv "SWARM_DB" t.db
  let c ← connect
  for k in ["tx", "auto"] do discard <| c.exec "insert into meta(k, v) values(?,'0')" [.text k]
  for i in [1:9] do discard <| c.exec "insert into meta(k, v) values(?,'100')" [.text s!"acct.{i}"]
  return c

/-- Runs `act` while a worker of `role` holds its transaction, then waits for it to end well. -/
def holding (t : T) (role : String) (act : IO Unit) : IO Unit := do
  let w ← spawnW t [role]
  discard <| w.stdout.getLine
  act
  waitAll #[w] s!"the {role} worker"

/-- `act` throws SQLITE_BUSY ("locked"); the ms it took. -/
def busy (msg : String) (act : IO Unit) : IO Nat := do
  let t0 ← IO.monoMsNow
  match ← (try act; pure none catch e => pure (some (toString e))) with
  | some e => if hasSub e "locked" then return (← IO.monoMsNow) - t0 else fail s!"{msg}: {e}"
  | none => fail s!"{msg}: it went through"

/-- The commits other connections made: changed by each (sqlite's `pragma data_version`). -/
def dataVersion (c : Conn) : IO (Array (Array Val)) := c.query "pragma data_version"

def pragma200 (c : Conn) : IO Unit := discard <| c.query "pragma busy_timeout=200"

/-- Concurrent transactions lose no update and each reads the latest value; one that can't get the write lock waits out
busy_timeout, then fails with SQLITE_BUSY, changing nothing and leaving no transaction open. -/
def sqlite_begin (t : T) : IO Unit := do
  let c ← setup t
  stress t [(N, ["tx"])] "sqlite_begin: no process fails (each waits within busy_timeout)"
  eq (← int c "select v from meta where k='tx'") (N * K) "sqlite_begin: no update in a transaction is lost"
  let seen (f : String) := int c s!"select {f} from event where kind='seen'"
  eq [← seen "count(*)", ← seen "count(distinct path)", ← seen "min(cast(path as integer))", ← seen "max(cast(path as integer))"]
    [N * K, N * K, 0, N * K - 1] "sqlite_begin: each transaction read the latest counter, and no two the same"
  pragma200 c
  holding t "hold" do
    let ms ← busy "sqlite_begin: waits out busy_timeout, then SQLITE_BUSY" <|
      sqliteRun c sc0 <| onMetas fun db => (setI db "seen.-1" (-1), ())
    eq (decide (ms ≥ 190)) true "sqlite_begin: it waits out busy_timeout"
  discard <| c.query "pragma busy_timeout=10000"
  sqliteRun c sc0 (Txn.done ())  -- no transaction was left open (else: cannot start a transaction within a transaction)
  eq (← int c "select count(*) from meta where k='seen.-1'") 0 "sqlite_begin: a BUSY changes nothing"

/-- Concurrent writes outside a transaction lose no update; one that can't get the lock waits out busy_timeout, then
fails with SQLITE_BUSY. -/
def sqlite_write (t : T) : IO Unit := do
  let c ← setup t
  stress t [(N, ["auto"])] "sqlite_write: no process fails (each waits within busy_timeout)"
  eq (← int c "select v from meta where k='auto'") (N * K) "sqlite_write: no update outside a transaction is lost"
  pragma200 c
  holding t "hold" do
    let ms ← busy "sqlite_write: waits out busy_timeout, then SQLITE_BUSY" <|
      discard (c.exec "update meta set v=cast(v as integer)+1 where k='tx'")
    eq (decide (ms ≥ 190)) true "sqlite_write: it waits out busy_timeout"
  eq (← int c "select v from meta where k='tx'") 0 "sqlite_write: a BUSY changes nothing"

/-- A transaction reads its own writes; reads never see part of a transaction, don't wait on the writer and don't see
its uncommitted write. -/
def sqlite_read (t : T) : IO Unit := do
  let c ← setup t
  discard <| c.exec "begin immediate"
  discard <| c.exec "update meta set v='5' where k='tx'"
  eq (← int c "select v from meta where k='tx'") 5 "sqlite_read: a transaction reads its own writes"
  discard <| c.exec "rollback"
  stress t [(3, ["move"]), (3, ["sum"])] "sqlite_read: no process fails"
  pragma200 c
  holding t "hold" do
    let t0 ← IO.monoMsNow
    eq (← int c "select v from meta where k='auto'") 0 "sqlite_read: a read doesn't see the writer's uncommitted write"
    eq (decide ((← IO.monoMsNow) - t0 < 100)) true "sqlite_read: a read doesn't wait on the writer"

/-- Every transaction of many processes at once commits whole (counters, transfers, readers, as sqlite_spec.lua ran
them together); a commit is the next version; a commit doesn't wait for a reader (WAL). -/
def sqlite_commit (t : T) : IO Unit := do
  let c ← setup t
  stress t [(N, ["tx", "auto"]), (3, ["move"]), (3, ["sum"])]
    "sqlite_begin, sqlite_write, sqlite_commit: no process fails (each waits within busy_timeout)"
  eq (← int c "select v from meta where k='tx'") (N * K) "sqlite_commit: every transaction's update is there"
  eq (← int c "select v from meta where k='auto'") (N * K) "sqlite_commit: every write outside one is there"
  eq (← int c sumSql) 80008 "sqlite_commit: the transfers are whole"
  holding t "hold" (pure ())
  eq (← int c "select v from meta where k='auto'") (-1) "sqlite_commit: the holder's commit is the next version"
  pragma200 c
  holding t "readhold" do
    let t0 ← IO.monoMsNow
    sqliteRun c sc0 <| onMetas fun db => (setI db "auto" 0, ())
    eq (decide ((← IO.monoMsNow) - t0 < 150)) true "sqlite_commit: a commit doesn't wait for a reader (WAL)"

/-- A transaction whose process is killed (SIGKILL) in it, or whose `Store.run` fails, leaves nothing and frees the lock. -/
def sqlite_rollback (t : T) : IO Unit := do
  let c ← setup t
  let w ← spawnW t ["victim"]
  discard <| w.stdout.getLine
  discard <| t.exec ["kill", "-KILL", toString w.pid]
  discard <| w.wait
  discard <| c.query "pragma busy_timeout=1000"
  sqliteRun c sc0 (Txn.done ())  -- the lock is free
  -- the write-back fails at the second row: the first is rolled back with it
  discard <| c.exec "create trigger nope before insert on meta when new.k='boom' begin select raise(abort, 'boom'); end"
  let failed ← try sqliteRun c sc0 (onMetas fun db => (setI (setI db "seen.-8" (-8)) "boom" 0, ())); pure false
    catch _ => pure true
  eq failed true "sqlite_rollback: the failing transaction fails"
  eq (← int c "select count(*) from meta where k in ('seen.-7', 'seen.-8')") 0 "sqlite_rollback: nothing of either is left"
  eq ((← c.query "pragma integrity_check")[0]?.bind (·[0]?) == some (.text "ok")) true "sqlite_rollback: the db is whole"

/-- A deferred transaction that has read, then writes after another connection's commit, gets SQLITE_BUSY
(BUSY_SNAPSHOT) at once, busy_timeout (10 s) not waited, and stays open: why `Store.run` never upgrades its read
transaction but writes in a new BEGIN IMMEDIATE one. -/
def deferred (t : T) : IO Unit := do
  let a ← setup t
  let b ← connect
  discard <| a.exec "begin"; discard <| a.query "select v from meta where k='auto'"
  discard <| b.exec "update meta set v=cast(v as integer)+1 where k='auto'"
  let ms ← busy "deferred: SQLITE_BUSY" <| discard (a.exec "update meta set v=cast(v as integer)+1 where k='auto'")
  eq (decide (ms < 1000)) true "deferred: SQLITE_BUSY at once"
  let opened ← try discard (a.exec "begin"); pure false catch _ => pure true
  eq opened true "deferred: the transaction stays open after it"
  discard <| a.exec "rollback"

/-- `pragma data_version` stays put while no other connection commits (across this connection's own transactions) and
changes when one does, read inside BEGIN IMMEDIATE too; a read-only `Store.run` takes no write lock, so it goes through at
once while another connection holds it (board #137). -/
def sqlite_version (t : T) : IO Unit := do
  let a ← setup t
  let b ← connect
  -- no fsync of the WAL under the write lock: a commit's wait on a busy disk held every other writer
  eq (toString (repr (← b.query "pragma synchronous"))) (toString (repr (#[#[Sqlite.Val.int 1]] : Array (Array Sqlite.Val)))) "connect: synchronous=normal"
  let v ← inTxn a "begin" (dataVersion a)
  sqliteRun a sc0 <| onMetas fun db => (setI db "tx" 1, ())
  eq ((← inTxn a "begin immediate" (dataVersion a)) == v) true "sqlite_version: unchanged by this connection's commits"
  discard <| b.exec "update meta set v='2' where k='tx'"
  eq ((← inTxn a "begin immediate" (dataVersion a)) == v) false "sqlite_version: changed by another connection's commit"
  pragma200 a
  holding t "hold" do
    let t0 ← IO.monoMsNow
    eq (← sqliteRun a sc0 <| onMetas fun db => (db, getI db "tx")) 2 "sqlite_version: a read-only transaction reads the last commit"
    eq (decide ((← IO.monoMsNow) - t0 < 150)) true "sqlite_version: a read-only transaction doesn't wait on the writer"

/-- The rows `sql` returns, each cell as JSON. -/
def rowsOf (c : Conn) (sql : String) : IO (List (List Json)) :=
  return (← c.query sql).toList.map (·.toList.map T.cell)

/-- The store's statements do on the real schema what `Stmt.run` says (Assumptions.lean's `SqlExec`, `SqlSelect`): an
insert gives each column it does not name its default and fails on a key a row has; an update by key sets only its
columns, and only in the row of that key (int and text keys); a delete takes only the row of its key; a select returns
every row; and the write-back of a loaded table, loaded again, is the step's rows. -/
def sqlite_dml (t : T) : IO Unit := do
  Shim.setenv "SWARM_DB" t.db
  let c ← connect
  discard <| c.exec "alter table task add column extra text default 'x'"
  let ins (i : Int) (title : String) : Stmt := .ins "task" ["id", "title", "state"] [.int i, .text title, .text "open"]
  runStmts c [ins 5 "a", ins 6 "b"]
  eq (← rowsOf c "select id, title, extra, priority from task order by id")
    [[toJson 5, toJson "a", toJson "x", toJson 2], [toJson 6, toJson "b", toJson "x", toJson 2]]
    "sqlite_dml: an insert gives the columns it does not name their defaults"
  let dup ← try runStmts c [ins 6 "c"]; pure false catch _ => pure true
  eq dup true "sqlite_dml: an insert of a key a row has fails"
  discard <| c.exec "update task set extra='y' where id=5"
  runStmts c [.upd "task" ["id"] [.int 5] ["title", "owner"] [.text "a2", .text "o"]]
  eq (← rowsOf c "select id, title, owner, extra from task order by id")
    [[toJson 5, toJson "a2", toJson "o", toJson "y"], [toJson 6, toJson "b", Json.null, toJson "x"]]
    "sqlite_dml: an update by key sets its columns in that row only"
  runStmts c [.del "task" ["id"] [.int 6]]
  eq (← rowsOf c "select id from task") [[toJson 5]] "sqlite_dml: a delete by key takes that row only"
  -- text keys, a two-column key
  runStmts c [.ins "agent" ["name"] [.text "ä1"], .ins "agent" ["name"] [.text "a10"],
    .ins "workspace" ["path", "agent"] [.text "/w", .text "a"], .ins "workspace" ["path", "agent"] [.text "/w", .text "b"]]
  runStmts c [.del "agent" ["name"] [.text "a10"], .upd "workspace" ["path", "agent"] [.text "/w", .text "b"] ["ro"] [.int 1]]
  eq (← rowsOf c "select name from agent") [[toJson "ä1"]] "sqlite_dml: a delete by a text key"
  eq (← rowsOf c "select agent, ro from workspace order by agent") [[toJson "a", toJson 0], [toJson "b", toJson 1]]
    "sqlite_dml: an update by a two-column key"
  eq (← rowsOf c "select count(*) from task") [[toJson 1]] "sqlite_dml: a select returns every row"
  -- the write-back, loaded again
  let old : List Task ← loadRows c
  let new := old.map (fun x => { x with title := some "z" }) ++ [{ id := 9, title := some "n" }]
  runStmts c (rowsPlan old new)
  let back : List Task ← loadRows c
  eq (decide (back = new)) true "sqlite_dml: load after the write-back is the step's rows"
  eq (← rowsOf c "select id, extra from task order by id") [[toJson 5, toJson "y"], [toJson 9, toJson "x"]]
    "sqlite_dml: the write-back keeps a column Lean does not know"

/-- `alter table add column` gives each row the column's default and appends it to `pragma table_info`, and fails on a
column the table has; the after migration copies after into a NULL deps as text and drops it (Assumptions.lean's
`SqlExec`, `SqlTableInfo`). -/
def sqlite_alter (t : T) : IO Unit := do
  Shim.setenv "SWARM_DB" t.db
  let c ← connect
  discard <| c.exec "alter table task drop column priority"
  discard <| c.exec "alter table agent drop column stay"
  discard <| c.exec "insert into task(id, title) values(1, 't')"
  discard <| c.exec "insert into agent(name) values('a')"
  runStmts c [.addCol "task" "priority int default 2", .addCol "agent" "stay text"]
  eq (← rowsOf c "select priority from task") [[toJson 2]] "sqlite_alter: a row gets the column's default"
  eq (← rowsOf c "select stay from agent") [[Json.null]] "sqlite_alter: a column with no default is NULL"
  eq ((← tableCols c "task").getLast?) (some "priority") "sqlite_alter: table_info lists the column last"
  let again ← try runStmts c [.addCol "task" "priority int default 2"]; pure false catch _ => pure true
  eq again true "sqlite_alter: adding a column the table has fails"
  discard <| c.exec "alter table task add column after int"
  discard <| c.exec "insert into task(id, deps, after) values(2, null, 3), (3, 'x', 4), (4, null, null)"
  runStmts c [.dropAfter]
  eq (← rowsOf c "select id, deps from task order by id")
    [[toJson 1, Json.null], [toJson 2, toJson "3"], [toJson 3, toJson "x"], [toJson 4, Json.null]]
    "sqlite_alter: after fills a NULL deps, as text"
  eq ((← tableCols c "task").contains "after") false "sqlite_alter: after is dropped"

/-- The statement store (`Store.run`, sw-global §3) does on real sqlite what `Txn.onDb` does to the model: a keyed and
a last-n select read the rows the model's `Db.slice` picks, a decision's plan (`slicePlan`) writes what the model's
statements do, an appended event is an insert that takes the next id, and a guarded update changes a row only where its
condition holds and says so (`changes()`). -/
def sqlite_txn (t : T) : IO Unit := do
  Shim.setenv "SWARM_DB" t.db
  let c ← connect
  discard <| c.exec "insert or ignore into swarm(name) values('t')"
  let fix : Db := {
    agents := [{ name := "a1", status := some "idle" }, { name := "a2", status := some "working" }]
    tasks := [{ id := 1, title := some "one" }, { id := 2, title := some "two", owner := some "a2", state := .claimed }]
    events := (List.range 6).map fun i =>
      let who := if i % 2 == 0 then "a1" else "a2"
      let k := if i < 3 then "status" else "end"
      { id := i + 1, ts := some i, agent := some who, kind := some k }
    cursors := [{ agent := "a1", last_msg_id := some 0 }]
    taskNext := 3, msgNext := 1, eventNext := 7 }
  writeRows c sc0 fix
  let loaded : IO Db := do let d ← readTables c sc0 allTables; pure { d with taskNext := 0, msgNext := 0, eventNext := 0 }
  let norm (d : Db) : Db := { d with taskNext := 0, msgNext := 0, eventNext := 0 }
  let sels : List Sel := [{ table := .agent, cond := .eq "name" (.text "a1") },
    { table := .event, cond := .eq "agent" (.text "a1"), last := some 2 },
    { table := .event, cond := .and (.eq "kind" (.text "end")) (.gt "id" (.int 5)) },
    { table := .task, cond := .notNull "owner" }]
  let got ← sqliteRun c sc0 (Txn.slice sels)
  eq (decide (got = fix.slice sels [])) true "sqlite_txn: a select reads the rows the model's slice picks"
  eq (got.events.map (·.id)) [3, 5, 6] "sqlite_txn: the last two of a1's events and the end events past id 5"
  -- a decision's plan, with an event appended
  let step : Txn Unit := Txn.update [{ table := .agent, cond := .eq "name" (.text "a1") }] [] fun d =>
    ((d.setAgent "a1" ({ · with status := some "working" })).log 9 (some "a1") "status" none (some "working"), ())
  sqliteRun c sc0 step
  let (want, _) := step.onDb fix
  eq (decide (norm (← loaded) = norm want)) true "sqlite_txn: a plan writes what the model's statements do"
  eq ((← loaded).events.getLast?.map (·.id)) (some 7) "sqlite_txn: an appended event takes the next id"
  -- a guarded update: a claim that only an open task takes
  let claim : Txn Bool := Txn.guarded (.upd "task" ["id"] [.int 1] ["owner", "state"] [.text "a1", .text "claimed"]) (.null "owner")
  eq (← sqliteRun c sc0 claim) true "sqlite_txn: a guarded update where its condition holds changes the row"
  eq (← sqliteRun c sc0 claim) false "sqlite_txn: and where it does not, nothing"
  let (m1, b1) := claim.onDb want
  let (m2, b2) := claim.onDb m1
  eq (b1, b2) (true, false) "sqlite_txn: the model's guarded update says the same"
  eq (decide (norm (← loaded) = norm m2)) true "sqlite_txn: and leaves the same rows"
  -- a transaction that writes nothing leaves the db as it was
  let before ← loaded
  sqliteRun c sc0 (Txn.update [{ table := .agent, cond := .all }] [] fun d => (d, ()))
  eq (decide ((← loaded) = before)) true "sqlite_txn: a decision that changes nothing writes nothing"

/-- A board for the task transactions: deps, a queue, a hold, a landing task, a blocked one, a stop not yet read, a
held note, and ids whose digits prefix one another (#1, #12). -/
def taskFix : Db := {
  agents := [{ name := "a1", status := some "idle", ctx_tokens := some 1000 },
    { name := "a2", status := some "working", role := some "lander" }, { name := "c", status := some "idle" },
    { name := "gone", status := some "ended", ended := some 5 }]
  metas := [{ k := "comms", v := some "c" }, { k := "reuse_below", v := some "0" }]
  tasks := [{ id := 1, title := some "one", qpos := some 1 }, { id := 2, title := some "two", deps := some "1", qpos := some 2 },
    { id := 3, title := some "three", state := .claimed, owner := some "a1", lease_until := some 2000 },
    { id := 4, title := some "four", state := .done, owner := some "a2" },
    { id := 5, title := some "five", deps := some "4" },
    { id := 6, title := some "six", state := .landing, owner := some "a1", lander := some "a2", land_sha := some "abc" },
    { id := 7, title := some "seven", hold := some "wait" },
    { id := 8, title := some "eight", state := .blocked, owner := some "a1", question := some "which?" },
    { id := 9, title := some "nine", stop_to := some "a2", stop_msg := some 3 },
    { id := 10, title := some "ten", deps := some "9" },
    { id := 11, title := some "main red: x", state := .claimed, owner := some "a1" },
    { id := 12, title := some "twelve", qpos := some 3 }]
  events := [{ id := 1, ts := some 1, agent := some "a1", kind := some "queue", data := some "#1" },
    { id := 2, ts := some 2, agent := some "a2", kind := some "queue", data := some "#12" },
    { id := 3, ts := some 3, agent := some "a2", kind := some "queue", data := some "#2" },
    { id := 4, ts := some 4, agent := some "a1", kind := some "claim", data := some "#3 three" },
    { id := 5, ts := some 5, agent := some "a2", kind := some "task-note", path := some "#1", data := some "#1 hi" },
    { id := 6, ts := some 6, agent := some "a2", kind := some "task-note", path := some "#12", data := some "#12 other" }]
  msgs := [{ id := 1, ts := some 5, frm := some "a2", dest := some "#1", body := some "hi", kind := some "task-note" },
    { id := 2, ts := some 6, frm := some "a2", dest := some "#12", body := some "other", kind := some "task-note" },
    { id := 3, ts := some 7, frm := some "c", dest := some "a2", body := some "stop", urgent := some 1 }]
  cursors := [{ agent := "a1", last_msg_id := some 0 }, { agent := "a2", last_msg_id := some 1 }]
  taskNext := 13, msgNext := 4, eventNext := 7 }

/-- Every table in key order, the next ids zeroed (an insert with its id leaves the model's next as it was). -/
def normDb (d : Db) : Db :=
  { agents := sortRows d.agents, msgs := sortRows d.msgs, cursors := sortRows d.cursors, tasks := sortRows d.tasks,
    locks := sortRows d.locks, conflicts := sortRows d.conflicts, pairkeys := sortRows d.pairkeys,
    metas := sortRows d.metas, events := sortRows d.events, workspaces := sortRows d.workspaces, cis := sortRows d.cis,
    taskNext := 0, msgNext := 0, eventNext := 0 }

/-- An answer as text: ok, or the error. -/
def exText : Except String α → String
  | .ok _ => "ok"
  | .error e => e

/-- The task and queue commands on the statement store (board #70): each `TaskTxn` reads only a slice, yet leaves the
db and answers as its whole-db step (Tasks.lean, Queue.lean) did, on a board that exercises their reads. -/
def task_txns_match_their_steps (_ : T) : IO Unit := do
  let a1 : Tasks.Ctx := { me := "a1", now := 1000 }
  let a2 : Tasks.Ctx := { me := "a2", now := 1000 }
  let cc : Tasks.Ctx := { me := "c", now := 1000 }
  let same {α : Type} (name : String) (t : Txn (Except String α)) (f : Db → Db × Except String α) : IO Unit := do
    let (d1, r1) := t.onDb taskFix
    let (d2, r2) := f taskFix
    eq (exText r1) (exText r2) s!"task_txns: {name} answers as its step"
    eq (decide (normDb d1 = normDb d2)) true s!"task_txns: {name} leaves the db as its step"
  let claimStep (c : Tasks.Ctx) (id : Int) (db : Db) : Db × Except String (Tasks.Claimed × List Msg) :=
    match Tasks.claim c id "2h" db with
    | (db, .ok r) => let (db, ns) := Notes.takeHeld c.me c.now id db; (db, .ok (r, ns))
    | (db, .error e) => (db, .error e)
  for i in [1, 2, 3, 5, 7, 9, 10, 12, 99] do
    same s!"claim #{i}" (TaskTxn.claimTxn a1 i "2h") (claimStep a1 i)
  same "claim --force of a held task" (TaskTxn.claimTxn { cc with force := true } 7 "2h") (claimStep { cc with force := true } 7)
  same "claim by a new agent" (TaskTxn.claimTxn { a1 with me := "new" } 1 "2h") (claimStep { a1 with me := "new" } 1)
  same "add" (TaskTxn.add a1 { title := "x", deps := [1, 5] }) (Tasks.add a1 { title := "x", deps := [1, 5] })
  same "add, a missing dep" (TaskTxn.add a1 { title := "x", deps := [99] }) (Tasks.add a1 { title := "x", deps := [99] })
  same "after" (TaskTxn.after a1 1 [12, 5]) (Tasks.after a1 1 [12, 5])
  same "after, a cycle" (TaskTxn.after a1 9 [10]) (Tasks.after a1 9 [10])
  same "after, a long cycle" (TaskTxn.after a1 1 [2]) (Tasks.after a1 1 [2])
  same "priority" (TaskTxn.one 1 (Tasks.priority a1 1 1)) (Tasks.priority a1 1 1)
  same "renew" (TaskTxn.one 3 (Tasks.renew a1 3 "1h")) (Tasks.renew a1 3 "1h")
  for (c, i) in [(a1, 3), (a2, 6), (a1, 6), (a1, 11), (a2, 3)] do
    same s!"done #{i} by {c.me}" (TaskTxn.done { c with onBase := true } i "sha") (Queue.done { c with onBase := true } i "sha")
  same "land" (TaskTxn.land a1 3 "def" (some "a2")) (Tasks.land a1 3 "def" (some "a2"))
  same "unland" (TaskTxn.unland a2 6 "red") (Tasks.unland a2 6 "red")
  same "unland by a stranger" (TaskTxn.unland { a1 with me := "x" } 6 "red") (Tasks.unland { a1 with me := "x" } 6 "red")
  same "block" (TaskTxn.block a1 3 "q") (Tasks.block a1 3 "q")
  same "unblock" (TaskTxn.unblock cc 8 "yes") (Tasks.unblock cc 8 "yes")
  same "release" (TaskTxn.release a1 3 none) (Tasks.release a1 3 none)
  same "release --after" (TaskTxn.release a1 3 (some [2])) (Tasks.release a1 3 (some [2]))
  same "release from another" (TaskTxn.release cc 8 none) (Tasks.release cc 8 none)
  same "edit" (TaskTxn.edit cc 3 { title := some "new" }) (Tasks.edit cc 3 { title := some "new" })
  for (c, i) in [(a1, 1), (a1, 3), (a2, 3), (cc, 8), (a2, 6), (a1, 4)] do
    same s!"drop #{i} by {c.me}" (TaskTxn.drop c i) (Queue.drop c i)
  same "hold" (TaskTxn.one 1 (Queue.hold a1 1 "why")) (Queue.hold a1 1 "why")
  same "unhold" (TaskTxn.unhold cc 7) (Queue.unhold cc 7)
  same "unhold, not in charge" (TaskTxn.unhold a1 7) (Queue.unhold a1 7)
  same "rules set" (TaskTxn.setRules cc "be kind") (Tasks.setRules cc "be kind")
  same "rules set, not in charge" (TaskTxn.setRules a1 "be kind") (Tasks.setRules a1 "be kind")
  same "queue add" (TaskTxn.qadd a1 [5, 1] .back) (Queue.add a1 [5, 1] .back)
  same "queue add, front" (TaskTxn.qadd cc [5] (.before 12)) (Queue.add cc [5] (.before 12))
  same "queue add, moves another's" (TaskTxn.qadd a1 [12] .back) (Queue.add a1 [12] .back)
  same "queue rm" (TaskTxn.qrm a1 [1]) (Queue.rm a1 [1])
  same "queue rm, another's" (TaskTxn.qrm a1 [12]) (Queue.rm a1 [12])
  -- the views: what they read gives the answers the whole db gives
  let (_, sh) := (TaskTxn.showTxn 1).onDb taskFix
  eq ((Tasks.taskEvents sh 1).map (·.id)) ((Tasks.taskEvents taskFix 1).map (·.id)) "task_txns: show reads the task's events"
  eq ((Notes.notes sh 1).map (·.text)) ["hi"] "task_txns: and its notes, not #12's"
  eq ((Tasks.waiters sh 1).map (·.id)) ((Tasks.waiters taskFix 1).map (·.id)) "task_txns: and its waiters"
  let (_, qv) := TaskTxn.queueView.onDb taskFix
  eq ((Queue.queued qv).map fun t => Queue.whyNot qv t) ((Queue.queued taskFix).map fun t => Queue.whyNot taskFix t)
    "task_txns: swarm queue says why as the whole db does"
  eq ((Queue.staffing qv).map (·.id)) ((Queue.staffing taskFix).map (·.id)) "task_txns: and staffs the same"

/-- The claim on real sqlite (board #70): the store's guarded update takes an open task for one claimer; the next
claimer is refused, and the model says the same. -/
def sqlite_claim (t : T) : IO Unit := do
  Shim.setenv "SWARM_DB" t.db
  let c ← connect
  discard <| c.exec "insert or ignore into swarm(name) values('t')"
  let fix : Db := { taskFix with metas := [] }
  writeRows c sc0 fix
  let a1 : Tasks.Ctx := { me := "a1", now := 1000 }
  let a2 : Tasks.Ctx := { me := "a2", now := 1000 }
  eq (exText (← sqliteRun c sc0 (TaskTxn.claimTxn a1 1 "2h"))) "ok" "sqlite_claim: the first claimer wins"
  eq (exText (← sqliteRun c sc0 (TaskTxn.claimTxn a2 1 "2h"))) "task #1 is claimed, owned by a1"
    "sqlite_claim: the second is refused"
  let (m1, _) := (TaskTxn.claimTxn a1 1 "2h").onDb fix
  let (m2, r2) := (TaskTxn.claimTxn a2 1 "2h").onDb m1
  eq (exText r2) "task #1 is claimed, owned by a1" "sqlite_claim: the model refuses it too"
  let got ← readTables c sc0 allTables
  eq (decide (normDb got = normDb m2)) true "sqlite_claim: and the rows are the model's"
  -- a prefix read: the events about #1, not #12's
  let (_, want) := (TaskTxn.showTxn 1).onDb m2
  let got ← sqliteRun c sc0 (TaskTxn.showTxn 1)
  eq (got.events.map (·.id)) (want.events.map (·.id)) "sqlite_claim: show reads the events the model's prefix picks"
  eq (decide ((Tasks.taskEvents got 1).all fun e => (e.data.getD "").startsWith "#1 " || e.data == some "#1")) true
    "sqlite_claim: and the task's events among them are none of #12's"
  -- the guard itself: an update of a claimed task where it is open changes nothing
  let some r := got.find 1 | fail "sqlite_claim: no task 1"
  eq (← sqliteRun c sc0 (Txn.guarded (Row.put { r with owner := some "a2" }) (.and (.eq "state" (.text "open")) (.null "owner"))))
    false "sqlite_claim: the guard refuses a claimed task"

def tests : List Case := [
  ("sqlite_begin", sqlite_begin),
  ("sqlite_write", sqlite_write),
  ("sqlite_read", sqlite_read),
  ("sqlite_commit", sqlite_commit),
  ("sqlite_rollback", sqlite_rollback),
  ("sqlite_dml", sqlite_dml),
  ("sqlite_alter", sqlite_alter),
  ("sqlite_txn", sqlite_txn),
  ("task_txns_match_their_steps", task_txns_match_their_steps),
  ("sqlite_claim", sqlite_claim),
  ("deferred", deferred),
  ("sqlite_version", sqlite_version)]

end SwarmLean.Tests.Spec.Sqlite

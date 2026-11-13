import Tests.Cli.Fixture

/-! sqlite_spec.lua: the store assumption (Assumptions.lean's `Atomic`, and the sqlite behaviour its tags name) against
real sqlite through the code's own store: `connect` (WAL, a 10 s busy handler) and `sqliteTxn` (`Store.txn`: load
and apply in a read transaction; a change written under BEGIN IMMEDIATE, applied again if another connection committed
since), many processes at once. Each case carries the name a tag gives. The other
processes are this binary's `--sqlite <role> …` (`worker`), each on its own connection to $SWARM_DB. Counters and
accounts are meta rows. -/

namespace SwarmLean.Tests.Spec.Sqlite
open SwarmLean SwarmLean.Tests.Cli
open SwarmLean.Sqlite (Conn Val)

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

def sumSql : String := "select coalesce(sum(cast(v as integer)),0)*100 + count(*) from meta where k like 'acct.%'"

/-- Prints a line and flushes it: the parent waits for it. -/
def signal : IO Unit := do let o ← IO.getStdout; o.putStrLn "x"; o.flush

/-- A worker process's role. tx: K Store.txns adding one to meta tx, each logging the value it read (an event of kind
seen); `tx auto` adds one to meta auto outside a transaction after each. auto: K writes outside a transaction adding
one to meta auto. move <i>: K Store.txns moving 1 between two of eight accounts. sum: 4K reads of the accounts' total.
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
      sqliteTxn c [.«meta»] fun db => let v := getI db "tx"; ((setI db "tx" (v + 1)).log 0 none "seen" (some (toString v)) none, ())
      if both then discard <| c.exec "update meta set v=cast(v as integer)+1 where k='auto'"
  | "auto", [] =>
    for _ in [0:K] do discard <| c.exec "update meta set v=cast(v as integer)+1 where k='auto'"
  | "move", [i] =>
    let mut g := mkStdGen i.toNat!
    for _ in [0:K] do
      let (a, g1) := randNat g 1 8
      let (b, g2) := randNat g1 1 8
      g := g2
      sqliteTxn c [.«meta»] fun db =>
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
    discard <| c.exec "begin immediate"; discard <| c.exec "insert into meta values('seen.-7','-7')"
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
  for k in ["tx", "auto"] do discard <| c.exec "insert into meta values(?,'0')" [.text k]
  for i in [1:9] do discard <| c.exec "insert into meta values(?,'100')" [.text s!"acct.{i}"]
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

def pragma200 (c : Conn) : IO Unit := discard <| c.query "pragma busy_timeout=200"

/-- Concurrent Store.txns lose no update and each reads the latest value; one that can't get the write lock waits out
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
      sqliteTxn c [.«meta»] fun db => (setI db "seen.-1" (-1), ())
    eq (decide (ms ≥ 190)) true "sqlite_begin: it waits out busy_timeout"
  discard <| c.query "pragma busy_timeout=10000"
  sqliteTxn c [] fun db => (db, ())  -- no transaction was left open (else: cannot start a transaction within a transaction)
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

/-- A transaction reads its own writes; reads never see part of a Store.txn, don't wait on the writer and don't see
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

/-- Every Store.txn of many processes at once commits whole (counters, transfers, readers, as sqlite_spec.lua ran
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
    sqliteTxn c [.«meta»] fun db => (setI db "auto" 0, ())
    eq (decide ((← IO.monoMsNow) - t0 < 150)) true "sqlite_commit: a commit doesn't wait for a reader (WAL)"

/-- A transaction whose process is killed (SIGKILL) in it, or whose Store.txn fails, leaves nothing and frees the lock. -/
def sqlite_rollback (t : T) : IO Unit := do
  let c ← setup t
  let w ← spawnW t ["victim"]
  discard <| w.stdout.getLine
  discard <| t.exec ["kill", "-KILL", toString w.pid]
  discard <| w.wait
  discard <| c.query "pragma busy_timeout=1000"
  sqliteTxn c [] fun db => (db, ())  -- the lock is free
  -- the write-back fails at the second row: the first is rolled back with it
  discard <| c.exec "create trigger nope before insert on meta when new.k='boom' begin select raise(abort, 'boom'); end"
  let failed ← try sqliteTxn c [.«meta»] (fun db => (setI (setI db "seen.-8" (-8)) "boom" 0, ())); pure false
    catch _ => pure true
  eq failed true "sqlite_rollback: the failing Store.txn fails"
  eq (← int c "select count(*) from meta where k in ('seen.-7', 'seen.-8')") 0 "sqlite_rollback: nothing of either is left"
  eq ((← c.query "pragma integrity_check")[0]?.bind (·[0]?) == some (.text "ok")) true "sqlite_rollback: the db is whole"

/-- A deferred transaction that has read, then writes after another connection's commit, gets SQLITE_BUSY
(BUSY_SNAPSHOT) at once, busy_timeout (10 s) not waited, and stays open: why Store.txn never upgrades its read
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
changes when one does, read inside BEGIN IMMEDIATE too; a read-only Store.txn takes no write lock, so it goes through at
once while another connection holds it (board #137). -/
def sqlite_version (t : T) : IO Unit := do
  let a ← setup t
  let b ← connect
  let v ← inTxn a "begin" (dataVersion a)
  sqliteTxn a [.«meta»] fun db => (setI db "tx" 1, ())
  eq ((← inTxn a "begin immediate" (dataVersion a)) == v) true "sqlite_version: unchanged by this connection's commits"
  discard <| b.exec "update meta set v='2' where k='tx'"
  eq ((← inTxn a "begin immediate" (dataVersion a)) == v) false "sqlite_version: changed by another connection's commit"
  pragma200 a
  holding t "hold" do
    let t0 ← IO.monoMsNow
    eq (← sqliteTxn a [.«meta»] fun db => (db, getI db "tx")) 2 "sqlite_version: a read-only Store.txn reads the last commit"
    eq (decide ((← IO.monoMsNow) - t0 < 150)) true "sqlite_version: a read-only Store.txn doesn't wait on the writer"

def tests : List Case := [
  ("sqlite_begin", sqlite_begin),
  ("sqlite_write", sqlite_write),
  ("sqlite_read", sqlite_read),
  ("sqlite_commit", sqlite_commit),
  ("sqlite_rollback", sqlite_rollback),
  ("deferred", deferred),
  ("sqlite_version", sqlite_version)]

end SwarmLean.Tests.Spec.Sqlite

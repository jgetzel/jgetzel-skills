import Tests.Cli.Fixture

/-! db_spec.lua's asserts on the Lean's db layer (Real.lean's `connect`, `sqliteRun`, `Db.log`; Sqlite.lean's binding).
db.lua's own API has no Lean form for three of them, not ported: a bool parameter (Val has none), a nested tx joining
the outer one (a Lean step is one pure function in one transaction), and refusing a statement given fewer values than
it has `?` (Conn.query binds what it is given, sqlite reads the rest as NULL; every statement is the code's own). -/

namespace SwarmLean.Tests.Spec.Db
open SwarmLean SwarmLean.Tests.Cli SwarmLean.Sqlite
open Lean (Json toJson)

/-- The first row's first cell. -/
def one (c : Conn) (sql : String) (ps : List Val := []) : IO (Option Val) := do
  return (← c.query sql ps)[0]?.bind (·[0]?)

/-- The fixture's swarm and repo. -/
def sc (t : T) : Scope := { swarm := "t", repo := t.repo }

def test_values_and_params (t : T) : IO Unit := do
  Shim.setenv "SWARM_DB" (t.d ++ "/sub/swarm.db")
  let c ← connect
  discard <| c.exec "insert into meta(k,v) values(?,?)" [.text "n", .int 1794]
  discard <| c.exec "insert into meta(k,v) values(?,?)" [.text "neg", .int (-5)]
  discard <| c.exec "insert into meta(k,v) values(?,?)" [.text "f", .real 4.85]
  discard <| c.exec "insert into meta(k,v) values(?,?)" [.text "q?'x'", .text "it's ?"]
  -- not '1794.0': Python int()s it
  eq ((← one c "select v from meta where k='n'") == some (.text "1794")) true
  eq ((← one c "select v from meta where k='neg'") == some (.text "-5")) true
  eq ((← one c "select v from meta where k='f'") == some (.text "4.85")) true
  eq ((← one c "select v from meta where k=?" [.text "q?'x'"]) == some (.text "it's ?")) true
  -- a negative value is a value, not `--`
  eq ((← one c "select 10-? x" [.int (-5)]) == some (.int 15)) true
  eq ((← one c "select ? x" [.null]) == some .null) true
  -- a ? inside a literal is not a parameter
  eq (← c.query "select 1 from meta where k='a''?b'").size 0
  eq (← c.exec "update meta set v='z' where k like ?" [.text "%"]) 4
  let bad ← try discard (c.exec "insert into nope values(1)"); pure false catch _ => pure true
  eq bad true

def test_txn_rolls_back_on_error (t : T) : IO Unit := do
  Shim.setenv "SWARM_DB" t.db
  let c ← connect
  -- an error inside the transaction rolls back what it wrote and goes on up: the write-back of `gone` is done when
  -- the trigger fails `boom`'s
  discard <| c.exec "create trigger nope before insert on meta when new.k='boom' begin select raise(abort, 'boom'); end"
  let r ← try
      sqliteRun c (sc t) (Txn.update [{ table := .meta }] [] fun db =>
        ({ db with metas := db.metas ++ [{ k := "gone", v := some "1" }, { k := "boom" }] }, ()))
      pure false
    catch _ => pure true
  eq r true
  eq ((← one c "select count(*) n from meta where k like 'gone%'") == some (.int 0)) true
  eq (← sqliteRun c (sc t) (Txn.done 7)) 7

/-- A fresh db is at DB_VERSION; reconnecting changes nothing; an older binary refuses to write, and reads. -/
def test_db_version (t : T) : IO Unit := do
  Shim.setenv "SWARM_DB" t.db
  let c ← connect
  eq (← dbVersion c) DB_VERSION
  -- a db from before the version existed (0) is raised, its rows kept
  discard <| c.exec "pragma user_version=0"
  discard <| c.exec "insert into meta(k,v) values('keep','1')"
  let c ← connect
  eq (← dbVersion c) DB_VERSION
  eq ((← one c "select v from meta where k='keep'") == some (.text "1")) true
  -- current to current: a no-op
  let c ← connect
  eq (← dbVersion c) DB_VERSION
  -- a binary one version older: refused, naming both versions and build.sh; reads go on
  let w := Txn.update [{ table := .meta }] [] fun db => ({ db with metas := db.metas ++ [{ k := "new", v := some "1" }] }, ())
  let msg ← try sqliteRun c (sc t) w (DB_VERSION - 1); pure "" catch e => pure (toString e)
  has msg "has db version 0" "refusal"; has msg "at version 1" "refusal"; has msg "build.sh" "refusal"
  eq ((← one c "select count(*) from meta where k='new'") == some (.int 0)) true
  eq (← sqliteRun c (sc t) (Txn.done 5) (DB_VERSION - 1)) 5
  sqliteRun c (sc t) w
  eq ((← one c "select count(*) from meta where k='new'") == some (.int 1)) true

def test_after_migration_columns_and_log (t : T) : IO Unit := do
  Shim.setenv "SWARM_DB" t.db
  let c ← connect
  -- an old db with task.after: copied into deps, column dropped
  discard <| c.exec "alter table task add column after int"
  discard <| c.exec "insert into task(title, after) values('t', 3)"
  let c ← connect
  eq ((← tableCols c "task").contains "after") false
  eq ((← one c "select deps from task") == some (.text "3")) true
  for (tb, col) in columns do
    has (← tableCols c tb) ((col.splitOn " ").headD col) s!"{tb}.{col}"
  let now := (← Sqlite.now).toNat
  sqliteRun c (sc t) (Txn.update [] [.event] fun db => (db.log now (some "a") "join" none none, ()))
  let ev ← t.q1 "select * from event"
  eq (ev.f "agent") "a"; eq (ev.f "kind") "join"; eq (ev.f "path") Json.null
  eq (decide ((ev.f "ts").i ≥ now - 5)) true

/-- db.connect, eight at once, on fresh dbs and on old ones missing columns (board #33, Iso.migrate_ok): none fails.
Each is a swarm-lean process connecting (`board`). -/
def test_connect_eight_at_once (t : T) : IO Unit := do
  let bin ← swarmBin
  for trial in [1:13] do
    let db := s!"{t.d}/race{trial}/swarm.db"
    if trial % 2 == 0 then
      Shim.setenv "SWARM_DB" db
      let x ← connect
      discard <| x.exec "alter table task drop column base"; discard <| x.exec "alter table agent drop column stay"
    let mut cs := #[]
    for _ in [0:8] do
      cs := cs.push (← IO.Process.spawn { cmd := bin, args := #["board"], env := #[("SWARM_DB", some db)],
                                          stdout := .null, stderr := .piped, cwd := some t.repo })
    for ch in cs do
      let err ← ch.stderr.readToEnd
      -- a fresh db has no swarm: `board` refuses after connecting
      let code ← ch.wait
      unless code == 0 || (code == 1 && subIn err "no swarm on this machine") do
        fail s!"db.connect failed alongside others: {err}"

def tests : List Case := [
  ("test_values_and_params", test_values_and_params),
  ("test_txn_rolls_back_on_error", test_txn_rolls_back_on_error),
  ("test_after_migration_columns_and_log", test_after_migration_columns_and_log),
  ("test_connect_eight_at_once", test_connect_eight_at_once),
  ("test_db_version", test_db_version)]

end SwarmLean.Tests.Spec.Db

namespace SwarmLean.Sqlite

/-- A value in a SQLite cell or parameter. -/
inductive Val
  | null
  | int (i : Int)
  | real (f : Float)
  | text (s : String)
  deriving Inhabited, Repr, BEq

opaque ConnP : NonemptyType
/-- An open SQLite connection. -/
def Conn : Type := ConnP.type
instance : Nonempty Conn := ConnP.property

opaque StmtP : NonemptyType
/-- A prepared statement. -/
def Stmt : Type := StmtP.type
instance : Nonempty Stmt := StmtP.property

/-- Opens the database file at `path` (read-only when `ro`), with a 10 s busy timeout. -/
@[extern "swarm_db_open"] opaque Conn.open (path : @& String) (ro : Bool) : IO Conn
/-- The connection's last error text. -/
@[extern "swarm_db_errmsg"] opaque Conn.errmsg (c : @& Conn) : IO String
/-- Compiles one SQL statement. -/
@[extern "swarm_db_prepare"] opaque Conn.prepare (c : @& Conn) (sql : @& String) : IO Stmt
/-- The rows the last statement changed. -/
@[extern "swarm_db_changes"] opaque Conn.changes (c : @& Conn) : IO UInt64
@[extern "swarm_db_bind_null"] opaque Stmt.bindNull (s : @& Stmt) (i : UInt32) : IO Unit
@[extern "swarm_db_bind_int"] opaque Stmt.bindInt (s : @& Stmt) (i : UInt32) (v : Int64) : IO Unit
@[extern "swarm_db_bind_real"] opaque Stmt.bindReal (s : @& Stmt) (i : UInt32) (v : Float) : IO Unit
@[extern "swarm_db_bind_text"] opaque Stmt.bindText (s : @& Stmt) (i : UInt32) (v : @& String) : IO Unit
/-- Steps the statement: true when it produced a row. -/
@[extern "swarm_db_step"] opaque Stmt.stepRaw (s : @& Stmt) : IO UInt8
@[extern "swarm_db_column_count"] opaque Stmt.columnCount (s : @& Stmt) : IO UInt32
@[extern "swarm_db_column_name"] opaque Stmt.columnName (s : @& Stmt) (i : UInt32) : IO String
@[extern "swarm_db_column_type"] opaque Stmt.columnType (s : @& Stmt) (i : UInt32) : IO UInt32
@[extern "swarm_db_column_int"] opaque Stmt.columnInt (s : @& Stmt) (i : UInt32) : IO UInt64
@[extern "swarm_db_column_real"] opaque Stmt.columnReal (s : @& Stmt) (i : UInt32) : IO Float
@[extern "swarm_db_column_text"] opaque Stmt.columnText (s : @& Stmt) (i : UInt32) : IO String

/-- The local time of day of epoch second `t`, as `HH:MM`. -/
@[extern "swarm_hhmm"] opaque hhmm (t : Int64) : IO String
/-- Epoch seconds. -/
@[extern "swarm_now"] opaque now : IO UInt64
/-- Replaces this process with `file` (looked up on PATH) run as `args` (args[0] included); returns only on failure. -/
@[extern "swarm_execvp"] opaque execvp (file : @& String) (args : @& Array String) : IO Unit

/-- Binds parameter `i` (1-based). -/
def Stmt.bind (s : Stmt) (i : UInt32) : Val → IO Unit
  | .null => s.bindNull i
  | .int v => s.bindInt i (Int64.ofInt v)
  | .real v => s.bindReal i v
  | .text v => s.bindText i v

/-- The value `bind` hands SQLite: an int as `Int64.ofInt`, so one outside int64 wraps. -/
def Val.bound : Val → Val
  | .int v => .int (Int64.ofInt v).toInt
  | v => v

/-- A value's storage class: 0 NULL, 1 integer, 2 real, 3 text. -/
def Val.cls : Val → Nat
  | .null => 0 | .int _ => 1 | .real _ => 2 | .text _ => 3

/-- Column `i` of the current row. -/
def Stmt.column (s : Stmt) (i : UInt32) : IO Val := do
  match ← s.columnType i with
  | 1 => return .int (← s.columnInt i).toInt64.toInt
  | 2 => return .real (← s.columnReal i)
  | 5 => return .null
  | _ => return .text (← s.columnText i)

/-- Runs `sql` with `params`: every row it returns, as values in column order. -/
def Conn.query (c : Conn) (sql : String) (params : List Val := []) : IO (Array (Array Val)) := do
  let s ← c.prepare sql
  let mut i : UInt32 := 1
  for p in params do
    s.bind i p
    i := i + 1
  let n ← s.columnCount
  let mut rows := #[]
  while (← s.stepRaw) == 1 do
    let mut row := #[]
    for j in [0:n.toNat] do
      row := row.push (← s.column j.toUInt32)
    rows := rows.push row
  return rows

/-- Runs one statement for its effect: the rows it changed. -/
def Conn.exec (c : Conn) (sql : String) (params : List Val := []) : IO Nat := do
  discard <| c.query sql params
  return (← c.changes).toNat

/-- Runs statements separated by `;` (no `;` inside a literal), for the schema. -/
def Conn.script (c : Conn) (sql : String) : IO Unit := do
  for st in sql.splitOn ";" do
    if st.trimAscii.toString != "" then discard <| c.exec st

end SwarmLean.Sqlite

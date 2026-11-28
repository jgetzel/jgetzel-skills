import LSql.Value
/-! The SQL abstract syntax the parser produces and the executor runs (sqlite's lang_*.html, the subset lean-sqlite supports).
Names are kept as written; the executor compares them case-insensitively, as sqlite does. -/
namespace LSql

inductive FrameUnits where
  | rows | range | groups
  deriving DecidableEq, Repr, Inhabited

inductive FrameExclude where
  | noOthers | currentRow | group | ties
  deriving DecidableEq, Repr, Inhabited

inductive RaiseKind where
  | ignore | rollback | abort | fail
  deriving DecidableEq, Repr, Inhabited

inductive BinOp where
  | add | sub | mul | div | mod          -- + - * / %
  | concat                              -- ||
  | eq | ne | lt | le | gt | ge         -- = == / != <> / < / <= / > / >=
  | is | isNot                          -- IS, IS NOT (also IS NOT DISTINCT FROM / IS DISTINCT FROM)
  | and | or
  | bitAnd | bitOr | shl | shr          -- & | << >>
  deriving DecidableEq, Repr, Inhabited

inductive UnOp where
  | neg | pos | not | bitNot            -- - + NOT ~
  deriving DecidableEq, Repr, Inhabited

/-- LIKE, GLOB, REGEXP, MATCH (the last two parse; the executor reports them as unsupported). -/
inductive MatchOp where
  | like | glob | regexp | «match»
  deriving DecidableEq, Repr, Inhabited

inductive JoinKind where
  | inner | left | cross | right | full
  deriving DecidableEq, Repr, Inhabited

/-- UNION, UNION ALL, INTERSECT, EXCEPT. -/
inductive CompoundOp where
  | union | unionAll | intersect | except
  deriving DecidableEq, Repr, Inhabited

/-- The name of the call that carries an aggregate's `FILTER (WHERE f)` as its last argument (a name no SQL can
write). -/
def filterTag : String := "\x00FILTER"

/-- The call the compiler wraps a json_each/json_tree `value` column in: its arguments are the value and the row's
`type`, so a JSON function sees an array or object value as JSON (sqlite's subtype). -/
def jsonValueTag : String := "\x00JSONVALUE"

mutual
inductive Expr where
  /-- A literal: NULL, an integer (one that does not fit an Int64 is a `real`), a real, a 'string', an X'blob'.
  `-9223372036854775808` is folded to `int` Int64's minimum. TRUE and FALSE are `int 1`/`int 0`. -/
  | lit (v : Value)
  /-- A column reference `[table.]name`. `dq`: written as a "double-quoted" identifier with no table, which sqlite reads as
  the string literal when no column has that name. `pos` (here and in `fn`, `window`): the byte offset of the reference in the
  statement it was parsed from, where sqlite3 reports an error in it. -/
  | col (table : Option String) (name : String) (dq : Bool) (pos : Option Nat := none)
  | bin (op : BinOp) (a b : Expr)
  | un (op : UnOp) (a : Expr)
  /-- A function call: `name(DISTINCT? args)`; `star` for `count(*)` (args empty). -/
  | fn (name : String) (distinct : Bool) (star : Bool) (args : List Expr) (pos : Option Nat := none)
  /-- `CAST(e AS type)`: the type name as written, words joined by one space (`VARCHAR(10)` keeps its parenthesis). -/
  | cast (e : Expr) (type : String)
  | collate (e : Expr) (collation : String)
  /-- `CASE [base] WHEN w THEN t ... [ELSE e] END`. -/
  | case (base : Option Expr) (whens : List (Expr × Expr)) (els : Option Expr)
  /-- `e [NOT] BETWEEN lo AND hi`. -/
  | between (e lo hi : Expr) (neg : Bool)
  /-- `e [NOT] IN (items)`; `e IN ()` has no items. -/
  | inList (e : Expr) (items : List Expr) (neg : Bool)
  /-- `e [NOT] IN (select)`, and `e IN table` as `SELECT * FROM table`. -/
  | inSelect (e : Expr) (q : Select) (neg : Bool)
  /-- `e [NOT] LIKE pat [ESCAPE esc]`, GLOB, ... -/
  | matches (op : MatchOp) (e pat : Expr) (esc : Option Expr) (neg : Bool)
  /-- `e ISNULL`, `e IS NULL` stays `bin .is e (lit null)`; `e NOTNULL` / `e NOT NULL` is `neg := true`. -/
  | isNull (e : Expr) (neg : Bool)
  /-- `[NOT] EXISTS (select)`. -/
  | «exists» (q : Select) (neg : Bool)
  /-- A scalar subquery `(select)`. -/
  | subquery (q : Select)
  /-- `?`, `?NNN`, `:name`, `@name`, `$name`: kept for the error message (lean-sqlite binds no parameters). -/
  | param (text : String)
  /-- A row value `(a, b, ...)` (two or more items). -/
  | row (items : List Expr)
  /-- A window function call `name(args) [FILTER (WHERE f)] OVER (window | name)`; a named window (WINDOW clause) is
  substituted by the parser (its `base` merged as sqlite does). -/
  | window (name : String) (distinct : Bool) (star : Bool) (args : List Expr) (filter : Option Expr) (over : Window) (pos : Option Nat := none)
  /-- `RAISE(IGNORE)`, `RAISE(ROLLBACK|ABORT|FAIL, 'message')` (in a trigger body). -/
  | raise (kind : RaiseKind) (msg : String)

/-- `OVER (PARTITION BY .. ORDER BY .. frame)`. -/
inductive Window where
  | mk (partition : List Expr) (orderBy : List OrderTerm) (frame : Option Frame)

/-- A frame bound: UNBOUNDED PRECEDING, e PRECEDING, CURRENT ROW, e FOLLOWING, UNBOUNDED FOLLOWING. -/
inductive FrameBound where
  | unboundedPreceding
  | preceding (e : Expr)
  | currentRow
  | following (e : Expr)
  | unboundedFollowing

/-- `ROWS|RANGE|GROUPS BETWEEN start AND end [EXCLUDE NO OTHERS|CURRENT ROW|GROUP|TIES]` (`ROWS start` alone is
`BETWEEN start AND CURRENT ROW`). -/
inductive Frame where
  | mk (units : FrameUnits) (start finish : FrameBound) (exclude : FrameExclude)

/-- One result column: `*`, `table.*`, or an expression with an optional alias (`span` is the expression's source text,
which sqlite uses as the column name when there is no alias). -/
inductive ResultCol where
  | star
  | tableStar (table : String)
  | expr (e : Expr) (alias : Option String) (span : String)

inductive FromItem where
  | table (name : String) (alias : Option String)
  | subquery (q : Select) (alias : Option String)
  /-- a table-valued function `name(args)` (json_each, json_tree, pragma_table_info, ...) -/
  | call (name : String) (args : List Expr) (alias : Option String)

/-- A join's right side: `kind item [ON e | USING (usingCols)]`; a comma join is `cross`; NATURAL is `usingCols = ["*"]`
(the columns the two sides share). -/
inductive Join where
  | mk (kind : JoinKind) (item : FromItem) (on : Option Expr) (usingCols : List String)

inductive OrderTerm where
  /-- `e [COLLATE c] [ASC|DESC] [NULLS FIRST|LAST]`; `nullsFirst` none: the default (first for ASC, last for DESC). -/
  | mk (e : Expr) (desc : Bool) (nullsFirst : Option Bool)

inductive Core where
  /-- `SELECT [DISTINCT|ALL] cols [FROM from joins] [WHERE w] [GROUP BY g] [HAVING h]`. -/
  | select (distinct : Bool) (cols : List ResultCol) («from» : Option FromItem) (joins : List Join) («where» : Option Expr)
      (groupBy : List Expr) (having : Option Expr)
  /-- `VALUES (..), (..)`. -/
  | values (rows : List (List Expr))

/-- A common table expression `name [(cols)] AS [[NOT] MATERIALIZED] (select)`: `materialized`, as written (none: neither). -/
inductive Cte where
  | mk (name : String) (cols : List String) (q : Select) (materialized : Option Bool)

inductive Select where
  /-- `[WITH [RECURSIVE] ctes] core (op core)* [ORDER BY ..] [LIMIT e [OFFSET e | , e]]`. `LIMIT a, b` is offset a,
  limit b. -/
  | mk (recursive : Bool) (ctes : List Cte) (first : Core) (rest : List (CompoundOp × Core)) (orderBy : List OrderTerm)
      (limit : Option Expr) (offset : Option Expr)
end

instance : Inhabited Expr := ⟨.lit .null⟩
instance : Inhabited Core := ⟨.values []⟩
instance : Inhabited Select := ⟨.mk false [] default [] [] none none⟩

/-- ON CONFLICT algorithms of INSERT OR .. / UPDATE OR .. / REPLACE INTO. -/
inductive Conflict where
  | abort | fail | ignore | replace | rollback
  deriving DecidableEq, Repr, Inhabited

/-- A column definition in CREATE TABLE. `type`: the declared type as written, words joined by one space ("" when none). -/
structure ColumnDef where
  name : String
  type : String := ""
  primaryKey : Bool := false
  pkDesc : Bool := false
  autoincrement : Bool := false
  notNull : Bool := false
  unique : Bool := false
  default : Option Expr := none
  collate : Option String := none
  check : List Expr := []
  deriving Inhabited

/-- An indexed column of CREATE INDEX or a table's PRIMARY KEY / UNIQUE constraint (`name [COLLATE c] [ASC|DESC]`). -/
structure IndexedCol where
  name : String
  collate : Option String := none
  desc : Bool := false
  /-- an expression index's term (`name` is then its source text) -/
  expr : Option Expr := none
  /-- the byte offset of the column name in the statement it was parsed from -/
  pos : Option Nat := none
  deriving Inhabited

inductive TableConstraint where
  | primaryKey (cols : List IndexedCol) (autoincrement : Bool)
  | unique (cols : List IndexedCol)
  | check (e : Expr)
  /-- FOREIGN KEY: parsed and ignored (sqlite does not enforce it unless PRAGMA foreign_keys=ON). -/
  | foreignKey
  /-- the table option STRICT (written after the column list) -/
  | strict
  deriving Inhabited

/-- `ON CONFLICT [(cols) [WHERE w]] DO NOTHING | DO UPDATE SET .. [WHERE w]`; `update none` is DO NOTHING. -/
structure Upsert where
  target : List IndexedCol := []
  targetWhere : Option Expr := none
  update : Option (List (String × Expr) × Option Expr) := none
  deriving Inhabited

inductive TriggerTiming where
  | before | after | insteadOf
  deriving DecidableEq, Repr, Inhabited

inductive TriggerEvent where
  | insert | delete
  /-- `UPDATE [OF cols]` -/
  | update (cols : List String)
  deriving DecidableEq, Repr, Inhabited

inductive InsertSource where
  | values (rows : List (List Expr))
  | select (q : Select)
  | defaults
  deriving Inhabited

inductive Stmt where
  /-- `sqlText`: what sqlite stores in sqlite_schema.sql: "CREATE TABLE " followed by the source text from the table's
  name token to the end of the statement (no `;`), as build.c's sqlite3EndTable writes it. -/
  | createTable (name : String) (ifNotExists : Bool) (cols : List ColumnDef) (cons : List TableConstraint)
      (withoutRowid : Bool) (sqlText : String)
  /-- `CREATE TABLE name AS select`. -/
  | createTableAs (name : String) (ifNotExists : Bool) (q : Select)
  /-- `sqlText`: "CREATE INDEX " / "CREATE UNIQUE INDEX " followed by the source from the index name token on. -/
  | createIndex (name : String) (table : String) (cols : List IndexedCol) (unique : Bool) (ifNotExists : Bool)
      («where» : Option Expr) (sqlText : String)
  /-- `sqlText`: "CREATE VIEW " followed by the source from the view name token on. -/
  | createView (name : String) (ifNotExists : Bool) (cols : List String) (q : Select) (sqlText : String)
  | dropTable (name : String) (ifExists : Bool)
  | dropIndex (name : String) (ifExists : Bool)
  | dropView (name : String) (ifExists : Bool)
  /-- `INSERT [OR c] INTO t [(cols)] source [upsert clauses]` and `REPLACE INTO` (conflict .replace). -/
  | insert (conflict : Conflict) (table : String) (cols : List String) (src : InsertSource) (upserts : List Upsert)
  /-- `UPDATE [OR c] t [AS alias] SET col = e, .. [WHERE w]`. -/
  | update (conflict : Conflict) (table : String) (alias : Option String) (sets : List (String × Expr)) («where» : Option Expr)
  /-- `DELETE FROM t [AS alias] [WHERE w]`. -/
  | delete (table : String) (alias : Option String) («where» : Option Expr)
  | select (q : Select)
  | begin
  | commit
  | rollback
  /-- `PRAGMA name [= value | (value)]`; the value as written (a name, a number, a string's contents). -/
  | pragma (name : String) (value : Option String)
  /-- `ALTER TABLE t RENAME TO n` / `ADD [COLUMN] def`. -/
  | alterRename (table : String) (newName : String)
  | alterAddColumn (table : String) (col : ColumnDef) (colText : String)
  | vacuum
  /-- `REINDEX [name]`: a no-op (lean-sqlite's indexes never go stale). -/
  | reindex
  /-- `SAVEPOINT name`, `RELEASE [SAVEPOINT] name`, `ROLLBACK [TRANSACTION] TO [SAVEPOINT] name`. -/
  | savepoint (name : String)
  | release (name : String)
  | rollbackTo (name : String)
  /-- `CREATE [TEMP] TRIGGER [IF NOT EXISTS] name [BEFORE|AFTER|INSTEAD OF] event ON table [FOR EACH ROW] [WHEN w]
  BEGIN stmt; ... END`. `sqlText`: what sqlite stores in sqlite_schema.sql (check it with the real sqlite3). -/
  | createTrigger (name : String) (ifNotExists : Bool) (timing : TriggerTiming) (event : TriggerEvent) (table : String)
      («when» : Option Expr) (body : List Stmt) (sqlText : String)
  | dropTrigger (name : String) (ifExists : Bool)
  /-- `INSERT/UPDATE/DELETE ... RETURNING cols`: the statement, and the result columns read from each row it writes. -/
  | returning (s : Stmt) (cols : List ResultCol)
  /-- `ALTER TABLE t RENAME [COLUMN] old TO new`, `ALTER TABLE t DROP [COLUMN] c`. -/
  | alterRenameColumn (table old new : String)
  | alterDropColumn (table col : String)
  /-- `CREATE TEMP TABLE/VIEW/TRIGGER ...` (and an object named `temp.x`): the statement, in the temp schema. -/
  | temp (s : Stmt)
  deriving Inhabited

end LSql

import LSql.Ast
import LSql.Func
import LSql.Pager
import LSql.Lex
/-! The schema: tables, indexes and views, as sqlite_schema describes them (fileformat2.html §2.6). -/
namespace LSql

/-- sqlite compares identifiers case-insensitively (ASCII). -/
def nameEq (a b : String) : Bool :=
  a.utf8ByteSize == b.utf8ByteSize && go 0 a.utf8ByteSize
where
  go (i : Nat) : Nat → Bool
    | 0 => true
    | f+1 => foldCase (Lex.byteAt a i) == foldCase (Lex.byteAt b i) && go (i+1) f

structure Column where
  name : String
  type : String := ""
  aff : Aff := .blob
  notNull : Bool := false
  default : Option Expr := none
  coll : Collation := .binary
  pk : Bool := false
  deriving Inhabited

structure Table where
  name : String
  root : Pgno
  cols : Array Column
  /-- the INTEGER PRIMARY KEY column, an alias of the rowid -/
  ipk : Option Nat := none
  autoinc : Bool := false
  checks : List Expr := []
  sql : String
  /-- WITHOUT ROWID: the table is an index-format b-tree keyed by its PRIMARY KEY columns `pkCols` (with their
  collations and directions); each record holds the key columns, then the others in table order -/
  withoutRowid : Bool := false
  /-- in the temp schema (its pages in the pager's temp space) -/
  temp : Bool := false
  /-- STRICT: every value must have its column's type -/
  strict : Bool := false
  pkCols : Array Nat := #[]
  pkColls : Array Collation := #[]
  pkDesc : Array Bool := #[]
  deriving Inhabited

/-- The table column of each record field: the key columns, then the rest (a WITHOUT ROWID table; empty otherwise). -/
def Table.layout (t : Table) : Array Nat :=
  if !t.withoutRowid then #[] else
  t.pkCols ++ ((List.range t.cols.size).toArray.filter (!t.pkCols.contains ·))

/-- A WITHOUT ROWID table's key order. -/
def Table.pkKeyInfo (t : Table) : KeyInfo := { colls := t.pkColls, desc := t.pkDesc, limit := t.pkCols.size }

def Table.colIndex? (t : Table) (n : String) : Option Nat := t.cols.findIdx? (nameEq ·.name n)

/-- A STRICT table's type error for a row (after affinity), if any. -/
def Table.strictError (t : Table) (row : Array Value) : Option String :=
  if !t.strict then none else
  t.cols.toList.zipIdx.findSome? fun (c, i) =>
    let v := row.getD i .null
    let ok := match upperAscii c.type, v with
      | _, .null => true
      | "ANY", _ => true
      | "INT", .int _ | "INTEGER", .int _ => true
      | "REAL", .real _ | "REAL", .int _ => true
      | "TEXT", .text _ => true
      | "BLOB", .blob _ => true
      | _, _ => t.ipk == some i
    if ok then none else
    some s!"cannot store {upperAscii v.typeName} value in {upperAscii c.type} column {t.name}.{c.name}"

structure Index where
  name : String
  table : String
  root : Pgno
  /-- the indexed columns of the table -/
  cols : Array Nat
  colls : Array Collation
  desc : Array Bool
  unique : Bool
  /-- the CREATE INDEX text; none for an index a UNIQUE or PRIMARY KEY constraint makes (sqlite_autoindex_T_N) -/
  sql : Option String
  /-- a partial index's WHERE -/
  pred : Option Expr := none
  /-- on a WITHOUT ROWID table, the key columns its entries end with (in place of a rowid) -/
  tail : Array Nat := #[]
  /-- an expression index's terms (none: the column `cols[i]` itself) -/
  exprs : Array (Option Expr) := #[]
  temp : Bool := false
  deriving Inhabited

def Index.hasExprs (i : Index) : Bool := i.exprs.any (·.isSome)

def Index.keyInfo (i : Index) : KeyInfo := { colls := i.colls, desc := i.desc }

structure View where
  name : String
  cols : List String
  q : Select
  sql : String
  temp : Bool := false
  deriving Inhabited

structure Trigger where
  name : String
  table : String
  timing : TriggerTiming
  event : TriggerEvent
  «when» : Option Expr
  body : List Stmt
  sql : String
  temp : Bool := false
  deriving Inhabited

structure Schema where
  tables : Array Table := #[]
  indexes : Array Index := #[]
  views : Array View := #[]
  triggers : Array Trigger := #[]
  deriving Inhabited

namespace Schema
/-- A name as the parser gives it: `main.`/`temp.` qualified (`"\x00main\x00t"`), or bare. -/
def splitQual (n : String) : Option Bool × String :=
  if n.startsWith "\x00" then
    match n.splitOn "\x00" with
    | ["", q, b] => (some (q == "temp"), b)
    | _ => (none, n)
  else (none, n)

/-- Looks a name up: in the schema it is qualified with, else temp first (a temp object hides a main one). -/
def lookup (xs : Array α) (name : α → String) (temp : α → Bool) (n : String) : Option α :=
  match splitQual n with
  | (some tq, b) => xs.find? fun x => temp x == tq && nameEq (name x) b
  | (none, b) => (xs.find? fun x => temp x && nameEq (name x) b).orElse fun _ => xs.find? fun x => nameEq (name x) b

def table? (s : Schema) (n : String) : Option Table := lookup s.tables (·.name) (·.temp) n
def view? (s : Schema) (n : String) : Option View := lookup s.views (·.name) (·.temp) n
def index? (s : Schema) (n : String) : Option Index := lookup s.indexes (·.name) (·.temp) n
def indexesOf (s : Schema) (t : String) : Array Index :=
  let temp := ((s.table? t).map (·.temp)).getD false
  let b := (splitQual t).2
  s.indexes.filter fun ix => nameEq ix.table b && ix.temp == temp
def trigger? (s : Schema) (n : String) : Option Trigger := lookup s.triggers (·.name) (·.temp) n
def exists? (s : Schema) (n : String) : Bool := (s.table? n).isSome || (s.view? n).isSome || (s.index? n).isSome
end Schema

/-- The sqlite_schema table, rooted at page 1. -/
def schemaTable : Table :=
  { name := "sqlite_schema", root := 1, sql := "CREATE TABLE sqlite_schema(type text,name text,tbl_name text,rootpage int,sql text)",
    cols := #[{ name := "type", type := "text", aff := .text }, { name := "name", type := "text", aff := .text },
              { name := "tbl_name", type := "text", aff := .text }, { name := "rootpage", type := "int", aff := .integer },
              { name := "sql", type := "text", aff := .text }] }

/-- A table's columns and constraints from its CREATE TABLE: the INTEGER PRIMARY KEY, and the columns of each automatic
index (PRIMARY KEY that is not the rowid, UNIQUE), in the order sqlite numbers them. -/
def tableOfDef (name : String) (root : Pgno) (cols : List ColumnDef) (cons : List TableConstraint) (sql : String)
    (withoutRowid : Bool := false) : Except String (Table × List (List IndexedCol × Bool)) := do
  let colsA := cols.toArray
  let tablePk : Option (List IndexedCol × Bool) := cons.findSome? fun
    | .primaryKey cs ai => some (cs, ai)
    | _ => none
  let colPk := colsA.findIdx? (·.primaryKey)
  if colPk.isSome && tablePk.isSome then throw s!"table \"{name}\" has more than one primary key"
  if (colsA.filter (·.primaryKey)).size > 1 then throw s!"table \"{name}\" has more than one primary key"
  let pkCols : List String := match colPk, tablePk with
    | some i, _ => [(colsA.getD i default).name]
    | none, some (cs, _) => cs.map (·.name)
    | none, none => []
  for c in pkCols do
    unless colsA.any (nameEq ·.name c) do throw s!"no such column: {c}"
  if withoutRowid && pkCols.isEmpty then throw s!"PRIMARY KEY missing on table {name}"
  -- the rowid alias: a single-column PRIMARY KEY of type INTEGER, not DESC (none in a WITHOUT ROWID table)
  let ipk : Option Nat := if withoutRowid then none else match pkCols with
    | [c] =>
      match colsA.findIdx? (nameEq ·.name c) with
      | some i =>
        let cd := colsA.getD i default
        let desc := match colPk with
          | some _ => cd.pkDesc
          | none => match tablePk with | some (ic :: _, _) => ic.desc | _ => false
        if (upperAscii cd.type) == "INTEGER" && !desc then some i else none
      | none => none
    | _ => none
  let autoinc := colsA.any (·.autoincrement) || (match tablePk with | some (_, a) => a | none => false)
  if autoinc && ipk.isNone then throw "AUTOINCREMENT is only allowed on an INTEGER PRIMARY KEY"
  let strict := cons.any fun | .strict => true | _ => false
  -- a STRICT table's columns have one of its six types; ANY keeps values as they come
  if strict then
    for cd in colsA do
      if cd.type.isEmpty then throw s!"missing datatype for {name}.{cd.name}"
      unless ["INT", "INTEGER", "REAL", "TEXT", "BLOB", "ANY"].contains (upperAscii cd.type) do
        throw s!"unknown datatype for {name}.{cd.name}: \"{cd.type}\""
  let tcols := colsA.map fun cd =>
    let coll := (cd.collate.bind Collation.ofName?).getD .binary
    let aff := if strict && upperAscii cd.type == "ANY" then .blob else Aff.ofType cd.type
    { name := cd.name, type := cd.type, aff, notNull := cd.notNull, default := cd.default, coll,
      pk := pkCols.any (nameEq · cd.name) : Column }
  for cd in colsA do
    if let some c := cd.collate then
      if (Collation.ofName? c).isNone then throw s!"no such collation sequence: {c}"
  -- automatic indexes, in the order sqlite creates them: column constraints by column, then table constraints
  let colAuto : List (List IndexedCol × Bool) := cols.foldr (fun cd acc =>
    let pk := if cd.primaryKey && ipk.isNone && !withoutRowid then [([{ name := cd.name, desc := cd.pkDesc : IndexedCol }], true)] else []
    let uq := if cd.unique then [([{ name := cd.name : IndexedCol }], true)] else []
    pk ++ uq ++ acc) []
  let tabAuto : List (List IndexedCol × Bool) := cons.filterMap fun
    | .primaryKey cs _ => if ipk.isNone && !withoutRowid then some (cs, true) else none
    | .unique cs => some (cs, true)
    | _ => none
  let checks := cols.foldr (fun cd acc => cd.check ++ acc) [] ++ cons.filterMap fun | .check e => some e | _ => none
  -- a WITHOUT ROWID table's key: its PRIMARY KEY columns, in their order, NOT NULL
  let pkIcs : List IndexedCol := match colPk, tablePk with
    | some i, _ => [{ name := (colsA.getD i default).name, desc := (colsA.getD i default).pkDesc,
                      collate := (colsA.getD i default).collate }]
    | none, some (cs, _) => cs
    | none, none => []
  let pkCols := pkIcs.toArray.filterMap fun ic => colsA.findIdx? (nameEq ·.name ic.name)
  let pkColls := pkIcs.toArray.map fun ic => match ic.collate.bind Collation.ofName? with
    | some c => c
    | none => ((colsA.findIdx? (nameEq ·.name ic.name)).bind fun i => (tcols[i]?.map (·.coll))).getD .binary
  let tcols := if withoutRowid then tcols.mapIdx fun i c => if pkCols.contains i then { c with notNull := true } else c else tcols
  return ({ name, root, cols := tcols, ipk, autoinc, checks, sql, withoutRowid, strict,
            pkCols := if withoutRowid then pkCols else #[], pkColls := if withoutRowid then pkColls else #[],
            pkDesc := if withoutRowid then pkIcs.toArray.map (·.desc) else #[] }, colAuto ++ tabAuto)

/-- An index's column numbers, collations and directions in table `t`. -/
def indexCols (t : Table) (cols : List IndexedCol) : Except String (Array Nat × Array Collation × Array Bool) := do
  let mut ns := #[]
  let mut cs := #[]
  let mut ds := #[]
  for ic in cols do
    if ic.expr.isSome then
      -- an expression term: its own collation, else BINARY
      ns := ns.push 0
      let coll ← match ic.collate with
        | some c => match Collation.ofName? c with
          | some x => pure x
          | none => throw s!"no such collation sequence: {c}"
        | none => pure .binary
      cs := cs.push coll
      ds := ds.push ic.desc
      continue
    match t.colIndex? ic.name with
    | none => throw s!"no such column: {ic.name}"
    | some i =>
      ns := ns.push i
      let coll ← match ic.collate with
        | some c => match Collation.ofName? c with
          | some x => pure x
          | none => throw s!"no such collation sequence: {c}"
        | none => pure (t.cols.getD i default).coll
      cs := cs.push coll
      ds := ds.push ic.desc
  return (ns, cs, ds)

end LSql

import LSql.Compile
import LSql.Eval
import LSql.Parse
/-! Statements: the database's state as a value threaded through each statement (sqlite's build.c, insert.c, update.c,
delete.c, pragma.c roles). Statements run in `EStateM`, so a failed one hands back the state it reached and the pager's
statement journal undoes it; the state is never shared, so its page arrays update in place. -/
namespace LSql

/-- Where an error is reported: preparing a statement ("Parse error") or running it ("Error"). -/
inductive ErrKind where
  | parse | runtime
  deriving DecidableEq, Inhabited

structure Err where
  kind : ErrKind
  msg : String
  deriving Inhabited

structure DB where
  pager : Pager := {}
  schema : Schema := {}
  /-- the database file; none for :memory: -/
  path : Option String := none
  /-- inside BEGIN ... COMMIT -/
  inTxn : Bool := false
  lastRowid : Int64 := 0
  changes : Int64 := 0
  totalChanges : Int64 := 0
  journalMode : String := "delete"
  /-- open savepoints, innermost first: name, the pager and schema to go back to, and whether it began the transaction -/
  savepoints : List (String × Pager × Schema × Bool) := []
  /-- inside a trigger program: the NEW/OLD scope and their row -/
  trig : Option (Scope × Row) := none
  /-- the triggers running (a trigger does not fire itself again: recursive_triggers is off) -/
  firing : List String := []
  /-- the statement is a CREATE TEMP ... -/
  inTemp : Bool := false
  /-- the statement's time ('now'), Unix milliseconds, read by the shell before it runs -/
  nowMs : Option Int64 := none
  /-- RETURNING: the rows the statement writes (new rows; deleted ones for DELETE), when collecting -/
  returned : Option (Array Row) := none
  deriving Inhabited

/-- A database value with nothing in it, left in a field while the real one is out being changed (a closed constant). -/
def DB.placeholder : DB := {}

structure Result where
  names : Array String := #[]
  rows : Array Row := #[]
  deriving Inhabited

abbrev XS := EStateM Err DB

def parseErr {α : Type} (msg : String) : XS α := throw ⟨.parse, msg⟩
def runErr {α : Type} (msg : String) : XS α := throw ⟨.runtime, msg⟩
def liftP {α : Type} : Except String α → XS α
  | .ok a => pure a
  | .error e => parseErr e
def liftR {α : Type} : Except String α → XS α
  | .ok a => pure a
  | .error e => runErr e

def fuel0 : Nat := 100000

namespace DB

def env (db : DB) : Env := { pager := db.pager, lastRowid := db.lastRowid, changes := db.changes, totalChanges := db.totalChanges,
                              nowMs := db.nowMs, schema := db.schema }

end DB

/-! ## Reading and changing the state -/

@[inline] def schemaX : XS Schema := do return (← get).schema
/-- The scopes and frames every statement sees: a trigger program's NEW and OLD. -/
def DB.ctxScopes (db : DB) : List Scope := match db.trig with | some (sc, _) => [sc] | none => []
def DB.ctxFrames (db : DB) : Array Row := match db.trig with | some (_, r) => #[r] | none => #[]
@[inline] def envX : XS Env := do let db ← get; return { db.env with frames := db.ctxFrames }
@[inline] def scopesX : XS (List Scope) := do return (← get).ctxScopes
@[inline] def modPager (f : Pager → Pager) : XS Unit := modify fun db => { db with pager := f db.pager }
@[inline] def modSchema (f : Schema → Schema) : XS Unit := modify fun db => { db with schema := f db.schema }

def compileQ (q : Select) : XS (CSel × Array String × Array Aff) := do
  let s ← schemaX
  let ((cq, names, affs, _), _) ← liftP ((compileSelect { schema := s, scopes := ← scopesX } q fuel0).run {})
  return (cq, names, affs)

/-- Runs a query: its column names and rows. -/
def query (q : Select) : XS Result := do
  let (cq, names, _) ← compileQ q
  let rows ← liftR (runSel (← envX) cq fuel0)
  return { names, rows }

/-- Evaluates a constant expression (a DEFAULT). -/
def evalConst (e : Expr) : XS Value := do
  let s ← schemaX
  let ((c, _, _), _) ← liftP ((compileExpr { schema := s, scopes := ← scopesX } e fuel0).run {})
  liftR (eval (← envX) c fuel0)

/-! ## sqlite_schema -/

def bumpCookie : XS Unit := modPager fun p => { p with schemaCookie := p.schemaCookie + 1 }

/-- The schema table's root: sqlite_schema (page 1), or sqlite_temp_schema. -/
def schemaRoot (temp : Bool) : Pgno := if temp then tempRoot else 1

/-- The stored page number of a root (temp roots as sqlite_temp_schema shows them: page numbers of their own space). -/
def storedRoot (r : Pgno) : Int64 := (if isTempPg r then r - tempBit else r).toNat.toInt64

/-- Appends a row to sqlite_schema (rowid: one past the largest). -/
def addSchemaRow (type name tbl : String) (root : Pgno) (sql : Option String) (temp : Bool := false) : XS Unit := do
  let rec_ := encodeRecord #[.text type, .text name, .text tbl, .int (storedRoot root), match sql with | some s => .text s | none => .null]
  let sr := schemaRoot temp
  modPager fun p => BTree.tableInsert p sr ((BTree.tableMaxKey p sr).getD 0 + 1) rec_
  bumpCookie

/-- The sqlite_schema rows (or sqlite_temp_schema's): rowid and columns. -/
def schemaRowsOf (p : Pager) (temp : Bool := false) : Array (Int64 × Array Value) :=
  if temp && p.tpages.isEmpty then #[] else
  BTree.foldTable p (schemaRoot temp) #[] fun acc k r => acc.push (k, decodeRecord r)

/-- Deletes the schema rows with name (or, when `byTable`, tbl_name) `n`. -/
def dropSchemaRows (n : String) (byTable : Bool) (temp : Bool := false) : XS Unit := do
  let rows := schemaRowsOf (← get).pager temp
  let ks := rows.filterMap fun (k, vs) => if nameEq (vs.getD (if byTable then 2 else 1) .null).toText n then some k else none
  modPager fun p => ks.foldl (fun p k => BTree.tableDelete p (schemaRoot temp) k) p
  bumpCookie

/-- Rewrites the schema row named `n`. -/
def updateSchemaRow (n : String) (f : Array Value → Array Value) (temp : Bool := false) : XS Unit := do
  let rows := schemaRowsOf (← get).pager temp
  let upd := rows.filterMap fun (k, vs) => if nameEq (vs.getD 1 .null).toText n then some (k, encodeRecord (f vs)) else none
  modPager fun p => upd.foldl (fun p (k, r) => BTree.tableInsert p (schemaRoot temp) k r) p
  bumpCookie

/-! ## Rows: affinity, constraints, index entries -/

/-- A table's scope for compiling expressions over one of its rows (columns, then the rowid, from slot 0). -/
def tableScope (t : Table) : Scope :=
  { srcs := #[{ name := t.name, cols := t.cols.map (·.name), affs := t.cols.map (·.aff), colls := t.cols.map (·.coll),
                base := 0, rowid := some t.cols.size, hidden := t.cols.map fun _ => false }] }

/-- An index's key values for a row: its columns, or its expressions evaluated on the row (`t`: the table). -/
def keyVals (t : Table) (ix : Index) (row : Row) : Array Value :=
  if !ix.hasExprs then ix.cols.map (row.getD · .null) else
  ix.cols.mapIdx fun i c => match ix.exprs.getD i none with
    | none => row.getD c .null
    | some e =>
      match (compileExpr { schema := {}, scopes := [tableScope t] } e fuel0).run {} with
      | .ok ((ce, _, _), _) => match eval (({ pager := Pager.placeholder } : Env).push row) ce fuel0 with
        | .ok v => v
        | .error _ => .null
      | .error _ => .null

/-- The entry of index `ix` for a row (its key values, then the rowid). -/
def indexKey (t : Table) (ix : Index) (row : Row) (rowid : Int64) : ByteArray :=
  encodeRecord ((keyVals t ix row).push (.int rowid))

/-- The record stored for a table row (the INTEGER PRIMARY KEY's column is NULL: it is the rowid). -/
def recordOf (t : Table) (row : Row) : ByteArray :=
  encodeRecord (row.mapIdx fun i v => if t.ipk == some i then .null else v)

/-- The row an UPDATE replaces: its slots that the statement reads (`row`), its record and that record's fields, and
which columns the SET clauses change. -/
structure OldRow where
  row : Row
  record : ByteArray
  fields : Array (UInt64 × Nat)
  changed : Array Bool

/-- The record of an UPDATE's new row: the columns it leaves alone copied from the old record, the others encoded (a
column past the old record's end has its default). -/
def recordOver (t : Table) (row : Row) (o : OldRow) : ByteArray :=
  spliceRecord o.record o.fields t.cols.size (fun i => !o.changed.getD i true && t.ipk != some i) fun i =>
    if t.ipk == some i then .null
    else if o.changed.getD i true || i < o.fields.size then row.getD i .null
    else columnDefault (t.cols.getD i default)

def tableRow (t : Table) (rowid : Int64) (rec_ : ByteArray) : Row :=
  decodeRow t.cols.size t.ipk (t.cols.map (·.aff == .real)) (t.cols.map columnDefault) rowid rec_

/-- The rowid of another row with the same key in a UNIQUE index (NULLs never conflict). -/
def uniqueConflict (p : Pager) (t : Table) (ix : Index) (row : Row) (rowid : Int64) : Option Int64 :=
  let vals := keyVals t ix row
  if !ix.unique || vals.any (·.isNull) then none else
  let probe := encodeRecord vals
  let rids := scanIndex p ix.root ix.keyInfo probe probe vals.size none
  rids.find? (· != rowid)

def uniqueMsg (t : Table) (ix : Index) : String :=
  "UNIQUE constraint failed: " ++ ", ".intercalate (ix.cols.toList.map fun c => s!"{t.name}.{(t.cols.getD c default).name}")

/-- The slots of a row (its columns, then its rowid) that its index entries read: an index's columns, or all of them for
an index on expressions or a partial one. -/
def indexNeed (t : Table) (idxs : Array Index) : Array Bool :=
  if idxs.any fun ix => ix.hasExprs || ix.pred.isSome then Array.replicate (t.cols.size + 1) true else
  idxs.foldl (fun m ix => ix.cols.foldl (fun m c => m.setIfInBounds c true) m) (Array.replicate (t.cols.size + 1) false)

/-- A table row's slots that `need` marks, decoded from its record (the others NULL). -/
def tableRowNeed (t : Table) (need : Array Bool) (rowid : Int64) (rec_ : ByteArray) : Row :=
  fillRow (Array.replicate (t.cols.size + 1) .null) 0 t.cols.size t.ipk (t.cols.map (·.aff == .real))
    (t.cols.map columnDefault) need rowid rec_

/-- Removes a row (`row`: as stored, at least the slots `indexNeed` marks) and its index entries. -/
def deleteRowOf (idxs : Array Index) (t : Table) (row : Row) (rowid : Int64) (p : Pager) : Pager :=
  let p := idxs.foldl (fun p ix => BTree.indexDelete p ix.keyInfo ix.root (indexKey t ix row rowid)) p
  BTree.tableDelete p t.root rowid

/-- Removes a row and its index entries (`need`: `indexNeed`). -/
def deleteRowN (need : Array Bool) (idxs : Array Index) (t : Table) (rowid : Int64) (p : Pager) : Pager :=
  match BTree.tableFind p t.root rowid with
  | none => p
  | some c => deleteRowOf idxs t (tableRowNeed t need rowid c.payload) rowid p

/-- Removes a row and its index entries. -/
def deleteRowP (idxs : Array Index) (t : Table) (rowid : Int64) (p : Pager) : Pager :=
  deleteRowN (indexNeed t idxs) idxs t rowid p

/-- Whether a row (its slots, then its rowid) belongs in an index: always, unless a partial index's WHERE is not true. -/
def inIndex (s : Schema) (env : Env) (t : Table) (ix : Index) (frame : Row) : Bool :=
  match ix.pred with
  | none => true
  | some w =>
    match (compileExpr { schema := s, scopes := [tableScope t] } w fuel0).run {} with
    | .ok ((ce, _, _), _) => match eval (env.push frame) ce fuel0 with
      | .ok v => v.truth? == some true
      | .error _ => false
    | .error _ => false

/-- Each CHECK's name (CONSTRAINT name) or expression text, in source order, from the CREATE TABLE text. -/
def checkTexts (sql : String) : Array String :=
  go 0 default default #[] (sql.utf8ByteSize + 1)
where
  go (i : Nat) (prev2 prev : Lex.Token) (acc : Array String) : Nat → Array String
    | 0 => acc
    | f+1 =>
      let t := Lex.lexTok sql i
      if t.kind == .eof then acc else
      if t.kind == .kCHECK then
        let lp := Lex.lexTok sql t.e
        let close := matchParen lp.e 1 (sql.utf8ByteSize + 1)
        let txt := if prev2.kind == .kCONSTRAINT then (Lex.sub sql prev.s prev.e).replace "\"" "" else Lex.sub sql lp.e (close - 1)
        go close prev t (acc.push txt) f
      else go t.e prev t acc f
  matchParen (i depth : Nat) : Nat → Nat
    | 0 => i
    | f+1 =>
      let t := Lex.lexTok sql i
      if t.kind == .eof then t.e
      else if t.kind == .lp then matchParen t.e (depth + 1) f
      else if t.kind == .rp then (if depth == 1 then t.e else matchParen t.e (depth - 1) f)
      else matchParen t.e depth f

/-- The first failing CHECK constraint's message for a row (with its rowid in the last slot). -/
def checkRow (t : Table) (frame : Row) : XS (Option String) := do
  if t.checks.isEmpty then return none
  let s ← schemaX
  let texts := checkTexts t.sql
  let mut i := 0
  for c in t.checks do
    let ((ce, _, _), _) ← liftP ((compileExpr { schema := s, scopes := [tableScope t] } c fuel0).run {})
    let v ← liftR (eval ((← envX).push frame) ce fuel0)
    if v.truth? == some false then return some s!"CHECK constraint failed: {texts.getD i t.name}"
    i := i + 1
  return none

/-- Writes one row (constraints checked, conflicts resolved); false when OR IGNORE skipped it. -/
def writeRow (t : Table) (idxs : Array Index) (row : Row) (rowid : Int64) (conflict : Conflict)
    (oldRowid : Option Int64) (old : Option OldRow := none) : XS Bool := do
  -- NOT NULL
  let mut row := row
  for i in [0:t.cols.size] do
    let c := t.cols.getD i default
    if c.notNull && (row.getD i .null).isNull && t.ipk != some i then
      match conflict with
      | .ignore => return false
      | .replace =>
        match c.default with
        | some d => row := row.setIfInBounds i (Value.applyAff c.aff (← evalConst d))
        | none => runErr s!"NOT NULL constraint failed: {t.name}.{c.name}"
      | _ => runErr s!"NOT NULL constraint failed: {t.name}.{c.name}"
  if let some msg := t.strictError row then runErr msg
  if let some msg ← checkRow t (row.push (.int rowid)) then
    if conflict == .ignore then return false else runErr msg
  -- the rowid
  if oldRowid != some rowid then
    if (BTree.tableFind (← get).pager t.root rowid).isSome then
      match conflict with
      | .ignore => return false
      | .replace => modPager (deleteRowP idxs t rowid)
      | _ => runErr s!"UNIQUE constraint failed: {t.name}.{match t.ipk with | some i => (t.cols.getD i default).name | none => "rowid"}"
  -- UNIQUE indexes (a partial one only among the rows it holds)
  let s ← schemaX
  let frame := row.push (.int rowid)
  let holds := idxs.map fun ix => inIndex s ({ pager := Pager.placeholder } : Env) t ix frame
  for ix in idxs, h in holds do
    if !ix.unique || !h then continue
    match uniqueConflict (← get).pager t ix row (oldRowid.getD rowid) with
    | some other =>
      if other == rowid && oldRowid.isNone then continue
      match conflict with
      | .ignore => return false
      | .replace => modPager (deleteRowP idxs t other)
      | _ => runErr (uniqueMsg t ix)
    | none => pure ()
  -- the old row goes, then the new one and its index entries
  if let some o := oldRowid then
    modPager (match old with | some o' => deleteRowOf idxs t o'.row o | none => deleteRowP idxs t o)
  let rec_ := match old with
    | some o => recordOver t row o
    | none => recordOf t row
  modPager fun p =>
    let p := BTree.tableInsert p t.root rowid rec_
    (idxs.zip holds).foldl (fun p (ix, h) => if h then BTree.indexInsert p ix.keyInfo ix.root (indexKey t ix row rowid) else p) p
  return true

/-- sqlite_sequence's value for an AUTOINCREMENT table. -/
def seqOf (s : Schema) (p : Pager) (t : Table) : Int64 :=
  match s.table? "sqlite_sequence" with
  | none => 0
  | some st => BTree.foldTable p st.root 0 fun acc _ r =>
    if nameEq (recordColumn r 0).toText t.name then (match recordColumn r 1 with | .int i => i | _ => acc) else acc

def setSeq (t : Table) (v : Int64) : XS Unit := do
  match (← schemaX).table? "sqlite_sequence" with
  | none => pure ()
  | some st =>
    modPager fun p =>
      let hit := BTree.foldTable p st.root none fun acc k r => if nameEq (recordColumn r 0).toText t.name then some k else acc
      let k := hit.getD ((BTree.tableMaxKey p st.root).getD 0 + 1)
      BTree.tableInsert p st.root k (encodeRecord #[.text t.name, .int v])

/-- A new row's rowid: one past the largest (and past sqlite_sequence's for AUTOINCREMENT). -/
def newRowid (t : Table) : XS Int64 := do
  let db ← get
  let mx := (BTree.tableMaxKey db.pager t.root).getD 0
  let mx := if t.autoinc then max mx (seqOf db.schema db.pager t) else mx
  if mx == 9223372036854775807 then runErr "database or disk is full"
  return mx + 1

/-- RETURNING: notes a row the statement wrote. -/
def noteRow (r : Row) : XS Unit := modify fun db => { db with returned := db.returned.map (·.push r) }

def setChanges (n : Int64) : XS Unit :=
  modify fun db => { db with changes := n, totalChanges := db.totalChanges + n }

/-! ## Statements -/

/-- The rows a WHERE clause selects from a table: each row's columns then its rowid (NULL in a WITHOUT ROWID table). -/
def matching (t : Table) (w : Option Expr) : XS (Array Row) := do
  let cols := t.cols.toList.map fun c => ResultCol.expr (.col (some t.name) c.name false) none c.name
  let cols := if t.withoutRowid then cols else cols ++ [ResultCol.expr (.col (some t.name) "rowid" false) none "rowid"]
  let qn := "\x00" ++ (if t.temp then "temp" else "main") ++ "\x00" ++ t.name
  let q : Select := .mk false [] (.select false cols (some (.table qn (some t.name))) [] w [] none) [] [] none none
  let (cq, _, _) ← compileQ q
  let rows ← liftR (runSel (← envX) cq fuel0)
  return if t.withoutRowid then rows.map (·.push .null) else rows

/-- The rowids of the rows a WHERE clause selects from a rowid table. -/
def matchingRowids (t : Table) (w : Option Expr) : XS (Array Int64) := do
  let qn := "\x00" ++ (if t.temp then "temp" else "main") ++ "\x00" ++ t.name
  let cols := [ResultCol.expr (.col (some t.name) "rowid" false) none "rowid"]
  let q : Select := .mk false [] (.select false cols (some (.table qn (some t.name))) [] w [] none) [] [] none none
  let (cq, _, _) ← compileQ q
  let rows ← liftR (runSel (← envX) cq fuel0)
  return rows.filterMap fun r => match r.getD 0 .null with | .int k => some k | _ => none

/-! ### WITHOUT ROWID tables: an index-format tree whose records are the key columns, then the rest -/

def worRecord (t : Table) (row : Row) : ByteArray := encodeRecord (t.layout.map (row.getD · .null))
def worKey (t : Table) (row : Row) : ByteArray := encodeRecord (t.pkCols.map (row.getD · .null))
def worRowOf (t : Table) (r : ByteArray) : Row := worRow t.cols.size t.layout (t.cols.map (·.aff == .real)) (t.cols.map columnDefault) r

/-- An index's entry for a row: its columns, then the rowid (or, on a WITHOUT ROWID table, the key columns it lacks). -/
def entryVals (t : Table) (ix : Index) (row : Row) (rowid : Int64) : Array Value :=
  if ix.tail.isEmpty then (keyVals t ix row).push (.int rowid)
  else keyVals t ix row ++ ix.tail.map (row.getD · .null)

def idxEntry (t : Table) (ix : Index) (row : Row) (rowid : Int64) : ByteArray :=
  encodeRecord (entryVals t ix row rowid)

/-- The row of a WITHOUT ROWID table with the key of `row`. -/
def worFind (p : Pager) (t : Table) (row : Row) : Option Row :=
  let key := worKey t row
  match (BTree.Cursor.seekKey p t.pkKeyInfo t.root key).key p with
  | some r => if cmpRecords t.pkKeyInfo r key == .eq then some (worRowOf t r) else none
  | none => none

def worDeleteP (idxs : Array Index) (t : Table) (row : Row) (p : Pager) : Pager :=
  let p := idxs.foldl (fun p ix => BTree.indexDelete p ix.keyInfo ix.root (idxEntry t ix row 0)) p
  BTree.indexDelete p t.pkKeyInfo t.root (worRecord t row)

def pkMsg (t : Table) : String :=
  "UNIQUE constraint failed: " ++ ", ".intercalate (t.pkCols.toList.map fun c => s!"{t.name}.{(t.cols.getD c default).name}")

/-- Writes a row of a WITHOUT ROWID table, as writeRow does a rowid table's; `old`: the row it replaces. -/
def writeRowWor (t : Table) (idxs : Array Index) (row : Row) (conflict : Conflict) (old : Option Row) : XS Bool := do
  let mut row := row
  for i in [0:t.cols.size] do
    let c := t.cols.getD i default
    if c.notNull && (row.getD i .null).isNull then
      match conflict with
      | .ignore => return false
      | .replace =>
        match c.default with
        | some d => row := row.setIfInBounds i (Value.applyAff c.aff (← evalConst d))
        | none => runErr s!"NOT NULL constraint failed: {t.name}.{c.name}"
      | _ => runErr s!"NOT NULL constraint failed: {t.name}.{c.name}"
  if let some msg := t.strictError row then runErr msg
  if let some msg ← checkRow t row then
    if conflict == .ignore then return false else runErr msg
  let s ← schemaX
  let isOld (r : Row) : Bool := match old with
    | some o => cmpRecords t.pkKeyInfo (worKey t o) (worKey t r) == .eq
    | none => false
  -- the key
  if !isOld row then
    if let some other := worFind (← get).pager t row then
      match conflict with
      | .ignore => return false
      | .replace => modPager (worDeleteP idxs t other)
      | _ => runErr (pkMsg t)
  -- UNIQUE indexes: an entry with the same values names its row by the key columns
  for ix in idxs do
    if !ix.unique || !inIndex s ({ pager := Pager.placeholder } : Env) t ix row then continue
    let vals := keyVals t ix row
    if vals.any (·.isNull) then continue
    let probe := encodeRecord vals
    let p := (← get).pager
    match (BTree.Cursor.seekKey p ix.keyInfo ix.root probe).key p with
    | some e =>
      if cmpRecords { ix.keyInfo with limit := ix.cols.size } e probe == .eq then
        let fs := decodeRecord e
        let orow := ix.cols.size.fold (fun k _ (r : Row) => r.setIfInBounds (ix.cols.getD k 0) (fs.getD k .null))
          (Array.replicate (t.cols.size + 1) .null)
        let orow := ix.tail.size.fold (fun k _ (r : Row) => r.setIfInBounds (ix.tail.getD k 0) (fs.getD (ix.cols.size + k) .null)) orow
        if !isOld orow && !(cmpRecords t.pkKeyInfo (worKey t orow) (worKey t row) == .eq && old.isNone && false) then
          match conflict with
          | .ignore => return false
          | .replace => match worFind (← get).pager t orow with
            | some full => modPager (worDeleteP idxs t full)
            | none => pure ()
          | _ => runErr (uniqueMsg t ix)
    | none => pure ()
  if let some o := old then modPager (worDeleteP idxs t o)
  let rec_ := worRecord t row
  let ins := idxs.filter fun ix => inIndex s ({ pager := Pager.placeholder } : Env) t ix row
  modPager fun p =>
    let p := BTree.indexInsert p t.pkKeyInfo t.root rec_
    ins.foldl (fun p ix => BTree.indexInsert p ix.keyInfo ix.root (idxEntry t ix row 0)) p
  return true

/-! ### Triggers -/

/-- The scope of a trigger program on table `t`: NEW, then OLD (each the table's columns and rowid). -/
def trigScope (t : Table) : Scope :=
  let n := t.cols.size
  let src (name : String) (base : Nat) : SrcInfo :=
    { name, cols := t.cols.map (·.name), affs := t.cols.map (·.aff), colls := t.cols.map (·.coll), base,
      rowid := some (base + n), hidden := t.cols.map fun _ => false }
  { srcs := #[src "new" 0, src "old" (n + 1)] }

def evMatch (te ev : TriggerEvent) (setCols : List String) : Bool :=
  match te, ev with
  | .insert, .insert | .delete, .delete => true
  | .update ocols, .update _ => ocols.isEmpty || ocols.any fun c => setCols.any (nameEq · c)
  | _, _ => false

def isIgnore (e : Err) : Bool := e.msg.startsWith "\x01RAISE:IGNORE"

/-- A view as a table of its result columns (for INSTEAD OF triggers). -/
def viewTable (v : View) : XS Table := do
  let (_, names, affs) ← compileQ v.q
  let names := if v.cols.isEmpty then names else v.cols.toArray
  return { name := v.name, root := 0, sql := v.sql,
           cols := names.mapIdx fun i n => { name := n, aff := (affs.getD i .none) : Column } }

/-- The UPSERT clause a row conflicts under, and the existing row it conflicts with (rowid tables). -/
def upsertConflict (t : Table) (idxs : Array Index) (us : List Upsert) (row : Row) (rowid : Int64) (hasRowid : Bool) :
    XS (Option (Upsert × Row)) := do
  let p := (← get).pager
  let byRowid : Option Row := if !hasRowid then none else
    (BTree.tableFind p t.root rowid).map fun c => tableRow t rowid c.payload
  let byIndex (ix : Index) : Option Row := (uniqueConflict p t ix row rowid).bind fun o =>
    (BTree.tableFind p t.root o).map fun c => tableRow t o c.payload
  for u in us do
    if u.target.isEmpty then
      if let some r := byRowid then return some (u, r)
      for ix in idxs do
        if let some r := byIndex ix then return some (u, r)
    else
      let tcols ← u.target.toArray.mapM fun ic => match t.colIndex? ic.name with
        | some i => pure i
        | none => parseErr s!"no such column: {ic.name}"
      if tcols.size == 1 && t.ipk == tcols[0]? then
        if let some r := byRowid then return some (u, r)
      else
        match idxs.find? (fun ix => ix.unique && ix.cols.size == tcols.size && tcols.all ix.cols.contains) with
        | some ix => if let some r := byIndex ix then return some (u, r)
        | none => parseErr "ON CONFLICT clause does not match any PRIMARY KEY or UNIQUE constraint"
  return none

/-- A name as sqlite writes it in generated SQL: quoted unless a plain identifier. -/
def quoteName (s : String) : String :=
  let plain := !s.isEmpty && s.toList.all (fun c => c.isAlphanum || c == '_') && !(s.toList.headD '0').isDigit
  if plain then s else "\"" ++ s.replace "\"" "\"\"" ++ "\""

def createIndexOn (t : Table) (name : String) (cols : List IndexedCol) (unique : Bool) (sql : Option String)
    (pred : Option Expr) : XS Unit := do
  let (ns, cs, ds) ← liftP (indexCols t cols)
  let p0 := (← get).pager
  let s0 ← schemaX
  -- on a WITHOUT ROWID table an entry ends with the key columns it lacks, not a rowid
  let tail := if t.withoutRowid then t.pkCols.filter (!ns.contains ·) else #[]
  let exprs := cols.toArray.map (·.expr)
  let ix0 : Index := { name, table := t.name, root := 0, cols := ns, colls := cs, desc := ds, unique, sql, pred, tail, exprs }
  -- the columns a plain index reads; a partial or expression index reads them all
  let need := Array.replicate (t.cols.size + 1) (pred.isSome || ix0.hasExprs)
  let need := ns.foldl (fun m c => m.setIfInBounds c true) (need.setIfInBounds t.cols.size true)
  let rows := if t.withoutRowid then BTree.foldIndex p0 t.root #[] fun acc r => acc.push (worRow t.cols.size t.layout (t.cols.map (·.aff == .real)) (t.cols.map columnDefault) r)
    else
      let rc := t.cols.map (·.aff == .real)
      let dv := t.cols.map columnDefault
      let blank : Row := Array.replicate (t.cols.size + 1) .null
      BTree.foldTable p0 t.root #[] fun acc k r => acc.push (fillRow blank 0 t.cols.size t.ipk rc dv need k r)
  -- a partial index holds the rows its WHERE accepts
  let rows := if pred.isNone then rows else rows.filter fun r => inIndex s0 ({ pager := Pager.placeholder } : Env) t ix0 r
  -- a UNIQUE index on rows that repeat a key fails before anything is written
  if unique then
    let keys := rows.filterMap fun r =>
      let vs := keyVals t ix0 r
      if vs.any (·.isNull) then none else some vs
    let sorted := sortBy keys (cmpRowsColl cs)
    let dup := (List.range (sorted.size - 1)).any fun i =>
      cmpRowsColl cs (sorted.getD i #[]) (sorted.getD (i+1) #[]) == .eq
    if dup then runErr ("UNIQUE constraint failed: " ++ ", ".intercalate (ns.toList.map fun c => s!"{t.name}.{(t.cols.getD c default).name}"))
  let root ← modifyGet fun db => let (r, p) := BTree.create db.pager .index t.temp; (r, { db with pager := p })
  let ix : Index := { name, table := t.name, root, cols := ns, colls := cs, desc := ds, unique, sql, pred, tail, exprs, temp := t.temp }
  let ki := ix.keyInfo
  -- entries in key order, so each lands at the end of the last leaf
  let vals := sortBy (rows.map fun r => entryVals t ix r (match r.getD t.cols.size .null with | .int k => k | _ => 0)) (cmpEntries ki)
  let vals := vals.foldl (fun acc v => match acc.back? with
    | some prev => if cmpEntries ki prev v == .eq then acc else acc.push v
    | none => acc.push v) #[]
  modPager fun p => BTree.indexBuild p root (vals.map encodeRecord)
  addSchemaRow "index" name t.name root sql t.temp
  modSchema fun s => { s with indexes := s.indexes.push ix }

def createTable (name : String) (ifNotExists : Bool) (cols : List ColumnDef) (cons : List TableConstraint)
    (withoutRowid : Bool) (sql : String) : XS Unit := do
  let s ← schemaX
  let temp := (← get).inTemp
  -- a temp table may share a main object's name (it hides it)
  let taken := if temp then s.tables.any (fun t => t.temp && nameEq t.name name) || s.views.any (fun v => v.temp && nameEq v.name name)
    else s.exists? name
  if taken || nameEq name "sqlite_schema" || nameEq name "sqlite_master" then
    if ifNotExists then return
    if (s.index? name).isSome then parseErr s!"there is already an index named {name}"
    parseErr s!"table {name} already exists"
  if temp then modPager Pager.ensureTemp
  let colNames := cols.map (·.name)
  for c in colNames do
    if (colNames.filter (nameEq · c)).length > 1 then parseErr s!"duplicate column name: {c}"
  let (t0, autos) ← liftP (tableOfDef name 0 cols cons sql withoutRowid)
  -- sqlite_sequence first, for the first AUTOINCREMENT table
  if t0.autoinc && (s.table? "sqlite_sequence").isNone then
    let r ← modifyGet fun db => let (r, p) := BTree.create db.pager .table; (r, { db with pager := p })
    addSchemaRow "table" "sqlite_sequence" "sqlite_sequence" r (some "CREATE TABLE sqlite_sequence(name,seq)")
    let seqT : Table := { name := "sqlite_sequence", root := r, cols := #[{ name := "name" }, { name := "seq" }],
                          sql := "CREATE TABLE sqlite_sequence(name,seq)" }
    modSchema fun s => { s with tables := s.tables.push seqT }
  let root ← modifyGet fun db => let (r, p) := BTree.create db.pager (if withoutRowid then .index else .table) temp; (r, { db with pager := p })
  let t := { t0 with root, temp }
  addSchemaRow "table" name name root (some sql) temp
  modSchema fun s => { s with tables := s.tables.push t }
  let mut k := 0
  for (ics, _) in autos do
    k := k + 1
    createIndexOn t s!"sqlite_autoindex_{name}_{k}" ics true none none

def dropTable (name : String) (ifExists : Bool) : XS Unit := do
  let s ← schemaX
  let some t := s.table? name
    | if ifExists then return else parseErr s!"no such table: {name}"
  if nameEq name "sqlite_sequence" || nameEq name "sqlite_schema" then parseErr s!"table {name} may not be dropped"
  let idxs := s.indexesOfTable t
  modPager fun p => BTree.drop (idxs.foldl (fun p ix => BTree.drop p ix.root) p) t.root
  dropSchemaRows t.name true t.temp
  -- its sqlite_sequence row goes too
  if let some st := s.table? "sqlite_sequence" then
    modPager fun p =>
      let ks := BTree.foldTable p st.root #[] fun acc k r => if nameEq (recordColumn r 0).toText t.name then acc.push k else acc
      ks.foldl (fun p k => BTree.tableDelete p st.root k) p
  modSchema fun s => { s with tables := s.tables.filter (fun x => !(nameEq x.name t.name && x.temp == t.temp)),
                              indexes := s.indexes.filter (fun x => !(nameEq x.table t.name && x.temp == t.temp)),
                              triggers := s.triggers.filter (fun x => !(nameEq x.table t.name && x.temp == t.temp)) }

/-- The span of the `k`th token of `s`. -/
def nthTokenSpan (s : String) (k : Nat) : Nat × Nat :=
  go 0 (s.utf8ByteSize + 1) k
where
  go (i : Nat) : Nat → Nat → Nat × Nat
    | 0, _ => (i, i)
    | _, 0 => let t := Lex.lexTok s i; (t.s, t.e)
    | f+1, k+1 => go (Lex.lexTok s i).e f k

/-- Replaces bytes [a, b) of `s`. -/
def splice (s : String) (a b : Nat) (r : String) : String :=
  Lex.sub s 0 a ++ r ++ Lex.sub s b s.utf8ByteSize

/-- The span of the token after `ON` in a CREATE INDEX. -/
def onTableSpan (s : String) : Nat × Nat :=
  go 0 false (s.utf8ByteSize + 1)
where
  go (i : Nat) (afterOn : Bool) : Nat → Nat × Nat
    | 0 => (i, i)
    | f+1 =>
      let t := Lex.lexTok s i
      if t.kind == .eof then (i, i) else
      if afterOn then (t.s, t.e) else go t.e (t.kind == .kON) f

def dq (s : String) : String := "\"" ++ s.replace "\"" "\"\"" ++ "\""

def alterRename (tn new : String) : XS Unit := do
  let s ← schemaX
  let some t := s.table? tn | parseErr s!"no such table: {tn}"
  if s.exists? new then parseErr s!"there is already another table or index with this name: {new}"
  -- CREATE TABLE "new"(...): the name is the third token
  let (a, b) := nthTokenSpan t.sql 2
  let sql := splice t.sql a b (dq new)
  updateSchemaRow t.name (fun vs => #[vs.getD 0 .null, .text new, .text new, vs.getD 3 .null, .text sql]) t.temp
  let renameOn (s : String) : String := let (a, b) := onTableSpan s; splice s a b (dq new)
  for ix in s.indexesOf t.name do
    updateSchemaRow ix.name fun vs =>
      #[vs.getD 0 .null, vs.getD 1 .null, .text new, vs.getD 3 .null, match ix.sql with | some q => .text (renameOn q) | none => .null]
  modSchema fun s =>
    { s with tables := s.tables.map (fun x => if nameEq x.name tn then { x with name := new, sql := sql } else x),
             indexes := s.indexes.map fun ix => if nameEq ix.table tn then { ix with table := new, sql := ix.sql.map renameOn } else ix }

def alterAdd (tn : String) (cd : ColumnDef) (colText : String) : XS Unit := do
  let s ← schemaX
  let some t := s.table? tn | parseErr s!"no such table: {tn}"
  if (t.colIndex? cd.name).isSome then parseErr s!"duplicate column name: {cd.name}"
  if cd.primaryKey then parseErr "Cannot add a PRIMARY KEY column"
  if cd.unique then parseErr "Cannot add a UNIQUE column"
  if cd.notNull && cd.default.isNone then parseErr "Cannot add a NOT NULL column with default value NULL"
  -- the column's text goes before the last ")"
  let close := (List.range t.sql.utf8ByteSize).foldl (fun acc i => if Lex.byteAt t.sql i == 41 then i else acc) t.sql.utf8ByteSize
  let sql := splice t.sql close close (", " ++ colText)
  let col : Column := { name := cd.name, type := cd.type, aff := Aff.ofType cd.type, notNull := cd.notNull,
                        default := cd.default, coll := (cd.collate.bind Collation.ofName?).getD .binary }
  updateSchemaRow t.name (fun vs => vs.setIfInBounds 4 (.text sql)) t.temp
  modSchema fun s => { s with tables := s.tables.map fun x => if nameEq x.name tn then { x with cols := x.cols.push col, sql := sql } else x }

def pragma (name : String) (value : Option String) : XS Result := do
  let n := lowerAscii name
  let db ← get
  let s := db.schema
  let one (col : String) (v : Value) : Result := { names := #[col], rows := #[#[v]] }
  if let some arg := value then
    if let some (names, rows) := schemaPragma s n arg then return { names, rows }
  match n, value with
  | "table_info", some tn =>
    match s.table? tn with
    | none => return {}
    | some t =>
      let pkCols := t.cols.toList.zipIdx.filter (·.1.pk) |>.map (·.2)
      let rows := t.cols.mapIdx fun i c =>
        -- sqlite keeps its standard type names (sqlite3StdType) in upper case
        let ty := if ["ANY", "BLOB", "INT", "INTEGER", "REAL", "TEXT"].contains (upperAscii c.type) then upperAscii c.type else c.type
        #[.int i.toInt64, .text c.name, .text ty, .int (if c.notNull then 1 else 0), defaultText c.default,
          .int (match pkCols.idxOf? i with | some k => (k + 1).toInt64 | none => 0)]
      return { names := #["cid", "name", "type", "notnull", "dflt_value", "pk"], rows }
  | "index_list", some tn =>
    let idxs := (s.indexesOf tn).reverse
    let rows := idxs.mapIdx fun i ix =>
      #[.int i.toInt64, .text ix.name, .int (if ix.unique then 1 else 0),
        .text (if ix.sql.isSome then "c" else if isPkIndex s ix then "pk" else "u"), .int (if ix.pred.isSome then 1 else 0)]
    return { names := #["seq", "name", "unique", "origin", "partial"], rows }
  | "index_info", some iname =>
    match s.index? iname with
    | none => return {}
    | some ix =>
      let t := s.table? ix.table
      let rows := ix.cols.mapIdx fun i c => #[.int i.toInt64, .int c.toInt64,
        .text ((t.map fun t => (t.cols.getD c default).name).getD "")]
      return { names := #["seqno", "cid", "name"], rows }
  | "user_version", none => return one "user_version" (.int db.pager.userVersion.toNat.toInt64)
  | "user_version", some v =>
    modPager fun p => { p with userVersion := (Num.atoi64 v).value.toNatClampNeg.toUInt32 }
    return {}
  | "schema_version", none => return one "schema_version" (.int db.pager.schemaCookie.toNat.toInt64)
  | "page_size", _ => return one "page_size" (.int db.pager.geo.pageSize.toInt64)
  | "page_count", _ => return one "page_count" (.int db.pager.pages.size.toInt64)
  | "freelist_count", _ => return one "freelist_count" (.int db.pager.free.size.toInt64)
  | "encoding", _ => return one "encoding" (.text "UTF-8")
  | "journal_mode", v =>
    let mode := if db.path.isNone then "memory" else (v.map lowerAscii).getD db.journalMode
    modify fun db => { db with journalMode := mode }
    return one "journal_mode" (.text mode)
  | "foreign_keys", none => return one "foreign_keys" (.int 0)
  | _, _ => return {}

/-- The schema from sqlite_schema's rows (each object's CREATE statement parsed again). -/
def schemaOf (p : Pager) : Except Err Schema := do
  let rows := (schemaRowsOf p).map (fun r => (r, false)) ++ (schemaRowsOf p true).map (fun r => (r, true))
  let mut sch : Schema := {}
  let mut autos : Array (Table × List (List IndexedCol × Bool)) := #[]
  let err (m : String) : Except Err Unit := .error ⟨.parse, m⟩
  for ((_, vs), temp) in rows do
    let type := (vs.getD 0 .null).toText
    let name := (vs.getD 1 .null).toText
    let tbl := (vs.getD 2 .null).toText
    let root := match vs.getD 3 .null with | .int r => (if temp then tempBit else 0) + r.toNatClampNeg.toUInt32 | _ => 0
    match vs.getD 4 .null with
    | .text s =>
      match Parse.parseNext s 0 with
      | .ok (some (.createTable n _ cols cons wr txt, _)) =>
        match tableOfDef n root cols cons txt wr with
        | .ok (t, au) =>
          let t := { t with sql := s, temp }
          sch := { sch with tables := sch.tables.push t }
          autos := autos.push (t, au)
        | .error e => err e
      | .ok (some (.createIndex n tn cols unique _ pred _, _)) =>
        match sch.table? tn with
        | some t =>
          match indexCols t cols with
          | .ok (ns, cs, ds) =>
            let tail := if t.withoutRowid then t.pkCols.filter (!ns.contains ·) else #[]
            sch := { sch with indexes := sch.indexes.push { name := n, table := t.name, root, cols := ns, colls := cs,
                                                            desc := ds, unique, sql := some s, pred, tail,
                                                            exprs := cols.toArray.map (·.expr), temp } }
          | .error e => err e
        | none => err s!"malformed database schema ({name}) - no such table: {tn}"
      | .ok (some (.createView n _ cols q _, _)) =>
        sch := { sch with views := sch.views.push { name := n, cols, q, sql := s, temp } }
      | .ok (some (.createTrigger n _ tm ev _ w body _, _)) =>
        sch := { sch with triggers := sch.triggers.push { name := n, table := tbl, timing := tm, event := ev, «when» := w, body, sql := s, temp } }
      | .ok _ => err s!"malformed database schema ({name})"
      | .error e => err s!"malformed database schema ({name}) - {e.msg}"
    | _ =>
      -- an automatic index: sqlite_autoindex_T_N is its table's Nth
      if type == "index" then
        if let some (t, au) := autos.find? (nameEq ·.1.name tbl) then
          let k := ((name.splitOn "_").getLast?.bind String.toNat?).getD 1
          if let some (ics, _) := au[k - 1]? then
            match indexCols t ics with
            | .ok (ns, cs, ds) =>
              let tail := if t.withoutRowid then t.pkCols.filter (!ns.contains ·) else #[]
              sch := { sch with indexes := sch.indexes.push { name, table := t.name, root, cols := ns, colls := cs,
                                                              desc := ds, unique := true, sql := none, tail, temp } }
            | .error e => err e
  return sch


/-- `sql` with every identifier naming `old` replaced by `new` (ALTER TABLE RENAME COLUMN). -/
def renameIdent (sql old new : String) : String :=
  go 0 "" (sql.utf8ByteSize + 1)
where
  go (i : Nat) (acc : String) : Nat → String
    | 0 => acc ++ Lex.sub sql i sql.utf8ByteSize
    | f+1 =>
      let t := Lex.lexTok sql i
      if t.kind == .eof then acc ++ Lex.sub sql i sql.utf8ByteSize else
      let gap := Lex.sub sql i t.s
      let txt := Lex.sub sql t.s t.e
      let isName := Parse.isIdKind t.kind && nameEq (Parse.nameOf sql t) old
      go t.e (acc ++ gap ++ (if isName then new else txt)) f

/-- A CREATE TABLE's text without column `c`'s definition (and the comma before it, or after it when first). -/
def dropColumnSql (sql c : String) : String :=
  -- the column definitions: spans between commas at depth 1
  let (segs, _, _, _) := (List.range (sql.utf8ByteSize + 1)).foldl (fun (acc : Array (Nat × Nat) × Nat × Nat × Nat) _ =>
    let (segs, i, depth, start) := acc
    let t := Lex.lexTok sql i
    if t.kind == .eof then acc else
    match t.kind with
    | .lp => (segs, t.e, depth + 1, if depth == 0 then t.e else start)
    | .rp => if depth == 1 then (segs.push (start, t.s), t.e, 0, start) else (segs, t.e, depth - 1, start)
    | .comma => if depth == 1 then (segs.push (start, t.s), t.e, depth, t.e) else (segs, t.e, depth, start)
    | _ => (segs, t.e, depth, start)) (#[], 0, 0, 0)
  let isCol (a : Nat) : Bool :=
    let t := Lex.lexTok sql a
    Parse.isIdKind t.kind && nameEq (Parse.nameOf sql t) c
  match segs.findIdx? (fun (a, _) => isCol a) with
  | none => sql
  | some k =>
    let (a, b) := segs.getD k (0, 0)
    if k > 0 then
      -- from the comma that ends the previous definition
      let (_, pb) := segs.getD (k - 1) (0, 0)
      splice sql pb b ""
    else
      match segs[k+1]? with
      | some (na, _) => splice sql a (Lex.lexTok sql na).s ""
      | none => sql

def reloadSchema : XS Unit := do
  match schemaOf (← get).pager with
  | .ok sch => modify fun db => { db with schema := sch }
  | .error e => throw e

def renameColumn (tn old new : String) : XS Unit := do
  let s ← schemaX
  let some t := s.table? tn | parseErr s!"no such table: {tn}"
  if (t.colIndex? old).isNone then parseErr s!"no such column: \"{old}\""
  if (t.colIndex? new).isSome then parseErr s!"duplicate column name: {new}"
  -- every stored statement of the table's objects names the column anew
  let rows := schemaRowsOf (← get).pager t.temp
  let upd := rows.filterMap fun (k, vs) =>
    if nameEq (vs.getD 2 .null).toText t.name then
      match vs.getD 4 .null with
      | .text q => some (k, vs.setIfInBounds 4 (.text (renameIdent q old (quoteName new))))
      | _ => none
    else none
  modPager fun p => upd.foldl (fun p (k, vs) => BTree.tableInsert p (schemaRoot t.temp) k (encodeRecord vs)) p
  bumpCookie
  reloadSchema

def dropColumn (tn c : String) : XS Unit := do
  let s ← schemaX
  let some t := s.table? tn | parseErr s!"no such table: {tn}"
  let some i := t.colIndex? c | parseErr s!"no such column: \"{c}\""
  let cname := (t.cols.getD i default).name
  if (t.cols.getD i default).pk then parseErr s!"cannot drop PRIMARY KEY column: \"{cname}\""
  if (s.indexesOf t.name).any (fun ix => ix.sql.isNone && ix.cols.contains i) then parseErr s!"cannot drop UNIQUE column: \"{cname}\""
  if t.cols.size == 1 then parseErr s!"cannot drop column \"{cname}\": no other columns exist"
  if let some ix := (s.indexesOf t.name).find? (fun ix => !ix.hasExprs && ix.cols.contains i) then
    runErr s!"error in index {ix.name} after drop column: no such column: {cname}"
  let sql := dropColumnSql t.sql c
  -- every row loses the field
  let p := (← get).pager
  if t.withoutRowid then
    let j := (t.layout.findIdx? (· == i)).getD 0
    let recs := BTree.foldIndex p t.root #[] fun acc r => acc.push (encodeRecord ((decodeRecord r).eraseIdxIfInBounds j))
    modPager fun p => recs.foldl (fun p r => BTree.indexInsert p t.pkKeyInfo t.root r) (BTree.clear p t.root)
  else
    let recs := BTree.foldTable p t.root #[] fun acc k r => acc.push (k, encodeRecord ((decodeRecord r).eraseIdxIfInBounds i))
    modPager fun p => recs.foldl (fun p (k, r) => BTree.tableInsert p t.root k r) p
  updateSchemaRow t.name (fun vs => vs.setIfInBounds 4 (.text sql)) t.temp
  reloadSchema

mutual
/-- Runs the triggers of table `t` for one row: each whose timing and event match, and whose WHEN holds, runs its
statements with NEW and OLD bound (a trigger already running does not fire again). -/
def fire (tm : TriggerTiming) (ev : TriggerEvent) (t : Table) (newRow oldRow : Option Row) (setCols : List String) :
    Nat → XS Unit
  | 0 => runErr "too many levels of trigger recursion"
  | fuel+1 => do
    let db ← get
    let trs := db.schema.triggers.filter fun tr =>
      nameEq tr.table t.name && tr.timing == tm && evMatch tr.event ev setCols && !db.firing.contains tr.name
    if trs.isEmpty then return
    let nulls : Row := Array.replicate (t.cols.size + 1) .null
    let ctx := (trigScope t, (newRow.getD nulls) ++ (oldRow.getD nulls))
    for tr in trs do
      let (sTrig, sFiring, sRet) ← modifyGet fun db => ((db.trig, db.firing, db.returned),
        { db with trig := some ctx, firing := tr.name :: db.firing, returned := none })
      try
        let go ← match tr.when with
          | none => pure true
          | some w => do let v ← evalConst w; pure (v.truth? == some true)
        if go then
          for st in tr.body do
            let _ ← exec1 st fuel
        modify fun db => { db with trig := sTrig, firing := sFiring, returned := sRet }
      catch e =>
        modify fun db => { db with trig := sTrig, firing := sFiring, returned := sRet }
        throw e

/-- The rows of a VALUES list whose terms are all literals and whose rows are as wide as the first: what running it gives. -/
def literalRows (vs : List (List Expr)) : Option (Array (Array Value)) :=
  match vs with
  | [] => none
  | r0 :: _ =>
    vs.toArray.mapM fun r => do
      let row ← r.toArray.mapM fun | .lit v => some v | _ => none
      if row.size == r0.length then some row else none

def insert (conflict : Conflict) (qtn : String) (cols : List String) (src : InsertSource) (upserts : List Upsert) :
    Nat → XS Unit
  | 0 => runErr "too many levels of trigger recursion"
  | fuel+1 => do
  let tn := (Schema.splitQual qtn).2
  let s ← schemaX
  if nameEq tn "sqlite_schema" || nameEq tn "sqlite_master" then parseErr s!"table {tn} may not be modified"
  let (t, isView) ← match s.table? qtn with
    | some t => pure (t, false)
    | none => match s.view? qtn with
      | some v =>
        if !s.triggers.any (fun tr => nameEq tr.table tn && tr.timing == .insteadOf && tr.event == .insert) then
          parseErr s!"cannot modify {tn} because it is a view"
        pure (← viewTable v, true)
      | none => parseErr s!"no such table: {tn}"
  let idxs := s.indexesOfTable t
  if !upserts.isEmpty && t.withoutRowid then parseErr "lean-sqlite: upsert on a WITHOUT ROWID table is not supported"
  -- target columns (a "rowid" column names the rowid itself)
  -- (none given: the values are in column order, and the targets are not built)
  let direct := cols.isEmpty && !(src matches .defaults)
  let targets : Array (Option Nat) ← if cols.isEmpty then pure #[] else
    cols.toArray.mapM fun c => match t.colIndex? c with
      | some i => pure (some i)
      | none => if !t.withoutRowid && !isView && (nameEq c "rowid" || nameEq c "oid" || nameEq c "_rowid_") then pure none
        else parseErr s!"table {t.name} has no column named {c}"
  let rows ← match src with
    | .defaults => pure #[#[]]
    | .values vs => do
      match literalRows vs with
      | some rs => pure rs
      | none =>
        let (cq, _, _) ← compileQ (.mk false [] (.values vs) [] [] none none)
        liftR (runSel (← envX) cq fuel0)
    | .select q => do
      let (cq, _, _) ← compileQ q
      liftR (runSel (← envX) cq fuel0)
  let targets := if src matches .defaults then #[] else targets
  let width := if direct then t.cols.size else targets.size
  let hasTriggers := s.triggers.any (nameEq ·.table t.name)
  -- one row can only fail before it writes: the statement journal is not needed
  if rows.size ≤ 1 && !hasTriggers && upserts.isEmpty then modPager Pager.noStmtJournal
  let defaults ← if direct then pure #[] else t.cols.mapM fun c => match c.default with
    | some d => evalConst d
    | none => pure .null
  let mut n : Int64 := 0
  for r in rows do
    if r.size != width then
      if cols.isEmpty then parseErr s!"table {t.name} has {t.cols.size} columns but {r.size} values were supplied"
      else parseErr s!"{r.size} values for {targets.size} columns"
    let mut row := if direct then r else defaults
    let mut explicitRowid : Option Value := none
    if !direct then
      for (tgt, v) in targets.zip r do
        match tgt with
        | some i => row := row.setIfInBounds i v
        | none => explicitRowid := some v
    row := row.mapIdx fun i v => Value.applyAff (t.cols.getD i default).aff v
    if isView then
      try fire .insteadOf .insert t (some (row.push .null)) none [] fuel; n := n + 1
      catch e => if isIgnore e then pure () else throw e
      continue
    if t.withoutRowid then
      try
        fire .before .insert t (some (row.push .null)) none [] fuel
        if ← writeRowWor t idxs (row.push .null) conflict none then
          n := n + 1
          noteRow (row.push .null)
          fire .after .insert t (some (row.push .null)) none [] fuel
      catch e => if isIgnore e then pure () else throw e
      continue
    -- the rowid: the INTEGER PRIMARY KEY's value, or a "rowid" column's, else a new one
    let given := match t.ipk with
      | some i => let v := row.getD i .null; if v.isNull then explicitRowid else some v
      | none => explicitRowid
    let hasRowid := match given with | some v => !v.isNull | none => false
    let rowid ← match given with
      | some v => if v.isNull then newRowid t else match toRowid? v with
        | some k => pure k
        | none => runErr "datatype mismatch"
      | none => newRowid t
    let row2 := (match t.ipk with | some i => row.setIfInBounds i (.int rowid) | none => row).push (.int rowid)
    try
      fire .before .insert t (some row2) none [] fuel
      -- UPSERT: a conflict a clause names turns the insert into nothing, or into an update of the row it meets
      let up ← if upserts.isEmpty then pure none else upsertConflict t idxs upserts (row2.extract 0 t.cols.size) rowid hasRowid
      match up with
      | some (u, old) =>
        match u.update with
        | none => pure ()
        | some (sets, w) =>
          let sc ← scopesX
          let upScope : Scope := { srcs := #[
            { name := t.name, cols := t.cols.map (·.name), affs := t.cols.map (·.aff), colls := t.cols.map (·.coll),
              base := 0, rowid := some t.cols.size, hidden := t.cols.map fun _ => false },
            -- excluded.* only by its name: an unqualified column is the table's
            { name := "excluded", cols := t.cols.map (·.name), affs := t.cols.map (·.aff), colls := t.cols.map (·.coll),
              base := t.cols.size + 1, rowid := some (2 * t.cols.size + 1), hidden := t.cols.map fun _ => true }] }
          let frame := old ++ row2
          let env := (← envX).push frame
          let ok ← match w with
            | none => pure true
            | some w => do
              let ((cw, _, _), _) ← liftP ((compileExpr { schema := s, scopes := upScope :: sc } w fuel0).run {})
              pure ((← liftR (eval env cw fuel0)).truth? == some true)
          if ok then
            let oldRowid := match old.getD t.cols.size .null with | .int k => k | _ => 0
            let mut nrow := old.extract 0 t.cols.size
            let mut nr := oldRowid
            for (c, e) in sets do
              let ((ce, _, _), _) ← liftP ((compileExpr { schema := s, scopes := upScope :: sc } e fuel0).run {})
              let v ← liftR (eval env ce fuel0)
              match t.colIndex? c with
              | some i =>
                let v := Value.applyAff (t.cols.getD i default).aff v
                if t.ipk == some i then
                  match toRowid? v with
                  | some k => nr := k
                  | none => runErr "datatype mismatch"
                else nrow := nrow.setIfInBounds i v
              | none => parseErr s!"no such column: {c}"
            let full := (match t.ipk with | some i => nrow.setIfInBounds i (.int nr) | none => nrow).push (.int nr)
            let setCols := sets.map (·.1)
            fire .before (.update setCols) t (some full) (some old) setCols fuel
            if ← writeRow t idxs (full.extract 0 t.cols.size) nr .abort (some oldRowid) then
              n := n + 1
              noteRow full
              fire .after (.update setCols) t (some full) (some old) setCols fuel
      | none =>
        if ← writeRow t idxs (row2.extract 0 t.cols.size) rowid conflict none then
          modify fun db => { db with lastRowid := rowid }
          if t.autoinc then
            let db ← get
            let cur := seqOf db.schema db.pager t
            if rowid > cur then setSeq t rowid
          n := n + 1
          noteRow row2
          fire .after .insert t (some row2) none [] fuel
    catch e => if isIgnore e then pure () else throw e
  setChanges n

def update (conflict : Conflict) (qtn : String) (sets : List (String × Expr)) (w : Option Expr) : Nat → XS Unit
  | 0 => runErr "too many levels of trigger recursion"
  | fuel+1 => do
  let tn := (Schema.splitQual qtn).2
  let s ← schemaX
  let (t, isView) ← match s.table? qtn with
    | some t => pure (t, false)
    | none => match s.view? qtn with
      | some v =>
        if !s.triggers.any (fun tr => nameEq tr.table tn && tr.timing == .insteadOf && tr.event matches .update _) then
          parseErr s!"cannot modify {tn} because it is a view"
        pure (← viewTable v, true)
      | none => parseErr s!"no such table: {tn}"
  let idxs := s.indexesOfTable t
  let sc ← scopesX
  let targets ← sets.toArray.mapM fun (c, e) => do
    let tgt ← match t.colIndex? c with
      | some i => pure (some i)
      | none => if !t.withoutRowid && (nameEq c "rowid" || nameEq c "oid" || nameEq c "_rowid_") then pure none else parseErr s!"no such column: {c}"
    let ((ce, _, _), _) ← liftP ((compileExpr { schema := s, scopes := tableScope t :: sc } e fuel0).run {})
    pure (tgt, ce)
  let hasTriggers := s.triggers.any (nameEq ·.table t.name)
  if !isView && !t.withoutRowid && !hasTriggers && conflict != .replace then
    -- each row decodes the columns the statement reads; its new record copies the others
    let ks ← matchingRowids t w
    if ks.size ≤ 1 then modPager Pager.noStmtJournal
    let n := t.cols.size
    let all := !t.checks.isEmpty || t.strict || (← get).returned.isSome
    let need := if all then Array.replicate (n + 1) true else
      let need := Array.zipWith (· || ·) (neededSlots (n + 1) (targets.map (·.2))) (indexNeed t idxs)
      let need := t.cols.size.fold (fun i _ m => if (t.cols.getD i default).notNull then m.setIfInBounds i true else m) need
      need.setIfInBounds n true
    let changed := targets.foldl (fun m (tgt, _) => match tgt with
      | some i => m.setIfInBounds i true
      | none => m) (Array.replicate n false)
    let mut cnt : Int64 := 0
    for oldRowid in ks do
      let some c := BTree.tableFind (← get).pager t.root oldRowid | continue
      let old := tableRowNeed t need oldRowid c.payload
      let mut row := old.extract 0 n
      let mut nr := oldRowid
      for (tgt, ce) in targets do
        let v ← liftR (eval ((← envX).push old) ce fuel0)
        match tgt with
        | some i =>
          let v := Value.applyAff (t.cols.getD i default).aff v
          if t.ipk == some i then
            match toRowid? v with
            | some k => nr := k
            | none => if v.isNull then nr := ← newRowid t else runErr "datatype mismatch"
          else row := row.setIfInBounds i v
        | none =>
          match toRowid? v with
          | some k => nr := k
          | none => runErr "datatype mismatch"
      let row2 := match t.ipk with | some i => row.setIfInBounds i (.int nr) | none => row
      try
        let o : OldRow := { row := old, record := c.payload, fields := recordFields c.payload, changed }
        if ← writeRow t idxs row2 nr conflict (some oldRowid) (some o) then
          cnt := cnt + 1
          if all then noteRow (row2.push (.int nr))
      catch e => if isIgnore e then pure () else throw e
    setChanges cnt
    return
  let rows ← if isView then do
      let q : Select := .mk false [] (.select false [.star] (some (.table tn none)) [] w [] none) [] [] none none
      let (cq, _, _) ← compileQ q
      let rs ← liftR (runSel (← envX) cq fuel0)
      pure (rs.map (·.push .null))
    else matching t w
  if rows.size ≤ 1 && !hasTriggers then modPager Pager.noStmtJournal
  let setCols := sets.map (·.1)
  let mut n : Int64 := 0
  for old in rows do
    let oldRowid := match old.getD t.cols.size .null with | .int k => k | _ => 0
    let mut row := old.extract 0 t.cols.size
    let mut nr := oldRowid
    for (tgt, ce) in targets do
      let v ← liftR (eval ((← envX).push old) ce fuel0)
      match tgt with
      | some i =>
        let v := Value.applyAff (t.cols.getD i default).aff v
        if t.ipk == some i then
          match toRowid? v with
          | some k => nr := k
          | none => if v.isNull then nr := ← newRowid t else runErr "datatype mismatch"
        else row := row.setIfInBounds i v
      | none =>
        match toRowid? v with
        | some k => nr := k
        | none => runErr "datatype mismatch"
    let row2 := match t.ipk with | some i => row.setIfInBounds i (.int nr) | none => row
    let newFull := row2.push (if t.withoutRowid || isView then .null else .int nr)
    try
      if isView then
        fire .insteadOf (.update setCols) t (some newFull) (some old) setCols fuel
        n := n + 1
      else
        fire .before (.update setCols) t (some newFull) (some old) setCols fuel
        let wrote ← if t.withoutRowid then writeRowWor t idxs newFull conflict (some old)
          else writeRow t idxs row2 nr conflict (some oldRowid)
        if wrote then
          n := n + 1
          noteRow newFull
          fire .after (.update setCols) t (some newFull) (some old) setCols fuel
    catch e => if isIgnore e then pure () else throw e
  setChanges n

def delete (qtn : String) (w : Option Expr) : Nat → XS Unit
  | 0 => runErr "too many levels of trigger recursion"
  | fuel+1 => do
  let tn := (Schema.splitQual qtn).2
  let s ← schemaX
  let (t, isView) ← match s.table? qtn with
    | some t => pure (t, false)
    | none => match s.view? qtn with
      | some v =>
        if !s.triggers.any (fun tr => nameEq tr.table tn && tr.timing == .insteadOf && tr.event == .delete) then
          parseErr s!"cannot modify {tn} because it is a view"
        pure (← viewTable v, true)
      | none => parseErr s!"no such table: {tn}"
  let idxs := s.indexesOfTable t
  let hasTriggers := s.triggers.any (nameEq ·.table t.name)
  if w.isNone && !hasTriggers && !isView then
    -- the whole table: clear its trees
    let p := (← get).pager
    let n : Int64 := if t.withoutRowid then BTree.foldIndex p t.root 0 fun n _ => n + 1
      else BTree.foldTable p t.root 0 fun n _ _ => n + 1
    modPager fun p => idxs.foldl (fun p ix => BTree.clear p ix.root) (BTree.clear p t.root)
    setChanges n
    return
  if !hasTriggers && !isView && !t.withoutRowid && (← get).returned.isNone then
    -- only the rowids, and of each row only its index keys
    let ks ← matchingRowids t w
    modPager Pager.noStmtJournal
    let need := indexNeed t idxs
    modPager fun p => ks.foldl (fun p k => deleteRowN need idxs t k p) p
    setChanges ks.size.toInt64
    return
  let rows ← if isView then do
      let q : Select := .mk false [] (.select false [.star] (some (.table tn none)) [] w [] none) [] [] none none
      let (cq, _, _) ← compileQ q
      let rs ← liftR (runSel (← envX) cq fuel0)
      pure (rs.map (·.push .null))
    else matching t w
  modify fun db => { db with returned := db.returned.map (· ++ rows) }
  if !hasTriggers then
    -- deleting cannot fail
    modPager Pager.noStmtJournal
    if t.withoutRowid then modPager fun p => rows.foldl (fun p r => worDeleteP idxs t r p) p
    else
      let ks := rows.filterMap fun r => match r.getD t.cols.size .null with | .int k => some k | _ => none
      modPager fun p => ks.foldl (fun p k => deleteRowP idxs t k p) p
    setChanges rows.size.toInt64
    return
  let mut n : Int64 := 0
  for old in rows do
    try
      if isView then
        fire .insteadOf .delete t none (some old) [] fuel
      else
        fire .before .delete t none (some old) [] fuel
        if t.withoutRowid then modPager (worDeleteP idxs t old)
        else match old.getD t.cols.size .null with
          | .int k => modPager (deleteRowP idxs t k)
          | _ => pure ()
        fire .after .delete t none (some old) [] fuel
      n := n + 1
    catch e => if isIgnore e then pure () else throw e
  setChanges n

def createTableAs (n : String) (ine : Bool) (q : Select) : Nat → XS Unit
  | 0 => runErr "too many levels of trigger recursion"
  | fuel+1 => do
  if (← schemaX).exists? n then
    if ine then return else parseErr s!"table {n} already exists"
  let (cq, names, affs) ← compileQ q
  let rows ← liftR (runSel (← envX) cq fuel0)
  let typeOf : Aff → String
    | .integer => "INT" | .real => "REAL" | .numeric => "NUM" | .text => "TEXT" | _ => ""
  let defs := (names.zip affs).toList.map fun (nm, a) =>
    (({ name := nm, type := typeOf a } : ColumnDef), quoteName nm ++ (if typeOf a == "" then "" else " " ++ typeOf a))
  let sql := s!"CREATE TABLE {quoteName n}(" ++ ",".intercalate (defs.map (·.2)) ++ ")"
  createTable n false (defs.map (·.1)) [] false sql
  unless rows.isEmpty do insert .abort n [] (.values (rows.toList.map fun r => r.toList.map Expr.lit)) [] fuel
  setChanges 0

/-- Runs one statement (`fuel`: how deep triggers may nest). -/
def exec1 (st : Stmt) : Nat → XS Result
  | 0 => runErr "too many levels of trigger recursion"
  | fuel+1 => do
  match st with
  | .select q => query q
  | .insert c t cols src ups => insert c t cols src ups fuel; return {}
  | .update c t sets w => update c t sets w fuel; return {}
  | .delete t w => delete t w fuel; return {}
  | .createTable n ine cols cons wr sql => createTable n ine cols cons wr sql; return {}
  | .createTableAs n ine q => createTableAs n ine q fuel; return {}
  | .createIndex n tn cols unique ine pred sql =>
    let s ← schemaX
    if s.exists? n then
      if ine then return {}
      if (s.index? n).isSome then parseErr s!"index {n} already exists"
      parseErr s!"there is already a table named {n}"
    let some t := s.table? tn | parseErr s!"no such table: main.{tn}"
    createIndexOn t n cols unique (some sql) pred
    return {}
  | .createView n ine cols q sql =>
    if (← schemaX).exists? n then
      if ine then return {} else parseErr s!"view {n} already exists"
    let _ ← compileQ q
    let temp := (← get).inTemp
    if temp then modPager Pager.ensureTemp
    addSchemaRow "view" n n 0 (some sql) temp
    modSchema fun s => { s with views := s.views.push { name := n, cols, q, sql, temp } }
    return {}
  | .createTrigger n ine tm ev tn w body sql =>
    let s ← schemaX
    if (s.trigger? n).isSome then
      if ine then return {} else parseErr s!"trigger {n} already exists"
    match s.table? tn, s.view? tn with
    | some _, _ => if tm == .insteadOf then parseErr s!"cannot create INSTEAD OF trigger on table: {tn}"
    | none, some _ => if tm != .insteadOf then
        parseErr s!"cannot create {if tm == .before then "BEFORE" else "AFTER"} trigger on view: {tn}"
    | none, none => parseErr s!"no such table: main.{tn}"
    let tname := match s.table? tn with | some t => t.name | none => (s.view? tn).map (·.name) |>.getD tn
    let temp := (← get).inTemp
    if temp then modPager Pager.ensureTemp
    addSchemaRow "trigger" n tname 0 (some sql) temp
    modSchema fun s => { s with triggers := s.triggers.push { name := n, table := tname, timing := tm, event := ev, «when» := w, body, sql, temp } }
    return {}
  | .dropTrigger n ie =>
    match (← schemaX).trigger? n with
    | none => if ie then return {} else parseErr s!"no such trigger: {n}"
    | some tr =>
      dropSchemaRows n false tr.temp
      modSchema fun s => { s with triggers := s.triggers.filter fun x => !(nameEq x.name n && x.temp == tr.temp) }
      return {}
  | .dropTable n ie =>
    if ((← schemaX).view? n).isSome then parseErr s!"use DROP VIEW to delete view {n}"
    dropTable n ie; return {}
  | .dropIndex n ie =>
    match (← schemaX).index? n with
    | none => if ie then return {} else parseErr s!"no such index: {n}"
    | some ix =>
      if ix.sql.isNone then parseErr "index associated with UNIQUE or PRIMARY KEY constraint cannot be dropped"
      modPager fun p => BTree.drop p ix.root
      dropSchemaRows ix.name false ix.temp
      modSchema fun s => { s with indexes := s.indexes.filter fun x => !(nameEq x.name n && x.temp == ix.temp) }
      return {}
  | .dropView n ie =>
    match (← schemaX).view? n with
    | none => if ie then return {} else parseErr s!"no such view: {n}"
    | some v =>
      dropSchemaRows n false v.temp
      modSchema fun s => { s with views := s.views.filter (fun x => !(nameEq x.name n && x.temp == v.temp)),
                                  triggers := s.triggers.filter (!nameEq ·.table n) }
      return {}
  | .alterRename t n => alterRename t n; return {}
  | .alterAddColumn t cd txt => alterAdd t cd txt; return {}
  | .alterRenameColumn t o n => renameColumn t o n; return {}
  | .alterDropColumn t c => dropColumn t c; return {}
  | .temp s =>
    modify fun db => { db with inTemp := true }
    let r ← exec1 s fuel
    modify fun db => { db with inTemp := false }
    return r
  | .returning st cols =>
    let tn := match st with
      | .insert _ t _ _ _ => some t | .update _ t _ _ => some t | .delete t _ => some t | _ => none
    let some tn := tn | parseErr "RETURNING is only allowed on INSERT, UPDATE and DELETE"
    let s ← schemaX
    let some t := s.table? tn | parseErr s!"cannot use RETURNING on {tn}"
    let sc ← scopesX
    -- the RETURNING columns, compiled over the table's row before anything is written
    let mut ces : Array CExpr := #[]
    let mut names : Array String := #[]
    for rc in cols do
      match rc with
      | .star | .tableStar _ =>
        for k in [0:t.cols.size] do
          ces := ces.push (.col 0 k); names := names.push (t.cols.getD k default).name
      | .expr e alias span =>
        let ((ce, _, _), _) ← liftP ((compileExpr { schema := s, scopes := tableScope t :: sc } e fuel0).run {})
        ces := ces.push ce
        names := names.push (alias.getD (match e with | .col _ n _ => ((t.colIndex? n).map fun k => (t.cols.getD k default).name).getD n | _ => span))
    modify fun db => { db with returned := some #[] }
    let _ ← exec1 st fuel
    let rows ← modifyGet fun db => (db.returned.getD #[], { db with returned := none })
    let env ← envX
    let out ← rows.mapM fun r => liftR (ces.mapM fun ce => eval (env.push r) ce fuel0)
    return { names, rows := out }
  | .pragma n v => pragma n v
  | .vacuum | .reindex | .begin | .commit | .rollback | .savepoint _ | .release _ | .rollbackTo _ => return {}
end

/-- Opens a database from its file's bytes (empty: a new database). -/
def openBytes (path : Option String) (bytes : ByteArray) : Except Err DB := do
  let p ← match Pager.ofFile bytes with
    | .ok p => pure p
    | .error e => .error ⟨.runtime, e⟩
  let sch ← schemaOf p
  let roots := sch.tables.map (·.root) ++ sch.indexes.map (·.root)
  return { pager := p.loadRoots roots, schema := sch, path }

/-- Runs a statement atomically: on an error its changes are undone through the statement journal (and, outside a
transaction, the statement is a transaction of its own). Returns whether the file needs writing. -/
def runStmt (db : DB) (s : Stmt) : DB × Except Err Result × Bool :=
  match s with
  | .begin =>
    if db.inTxn then (db, .error ⟨.runtime, "cannot start a transaction within a transaction"⟩, false)
    else ({ db with inTxn := true, pager := db.pager.beginTxn }, .ok {}, false)
  | .commit =>
    if !db.inTxn then (db, .error ⟨.runtime, "cannot commit - no transaction is active"⟩, false)
    else ({ db with inTxn := false, pager := db.pager.endTxn, savepoints := [] }, .ok {}, true)
  | .rollback =>
    if !db.inTxn then (db, .error ⟨.runtime, "cannot rollback - no transaction is active"⟩, false)
    else
      let p := db.pager.rollbackTxn
      match schemaOf p with
      | .ok sch => ({ db with pager := p, schema := sch, inTxn := false, savepoints := [] }, .ok {}, false)
      | .error e => ({ db with pager := p, inTxn := false, savepoints := [] }, .error e, false)
  -- a savepoint keeps the state to go back to: the pager value itself (its arrays are copied on the next change)
  | .savepoint n =>
    let began := !db.inTxn
    let db := if began then { db with inTxn := true, pager := db.pager.beginTxn } else db
    ({ db with savepoints := (n, db.pager, db.schema, began) :: db.savepoints }, .ok {}, false)
  | .rollbackTo n =>
    match db.savepoints.dropWhile (!nameEq ·.1 n) with
    | [] => (db, .error ⟨.runtime, s!"no such savepoint: {n}"⟩, false)
    | sp@(_, p, sch, _) :: rest => ({ db with pager := p, schema := sch, savepoints := sp :: rest }, .ok {}, false)
  | .release n =>
    match db.savepoints.dropWhile (!nameEq ·.1 n) with
    | [] => (db, .error ⟨.runtime, s!"no such savepoint: {n}"⟩, false)
    | (_, _, _, began) :: rest =>
      if began && rest.isEmpty then ({ db with inTxn := false, pager := db.pager.endTxn, savepoints := [] }, .ok {}, true)
      else ({ db with savepoints := rest }, .ok {}, false)
  | s =>
    let inTxn := db.inTxn
    let sch0 := db.schema
    -- (outside a transaction, beginAutocommit also starts the statement journal)
    let db := { db with pager := if inTxn then db.pager.beginStmt else db.pager.beginAutocommit }
    match (exec1 s 64).run db with
    | .ok r db =>
      let writes := match s with | .select _ => false | .pragma _ none => false | _ => true
      let db := if inTxn then db else { db with pager := db.pager.endTxn }
      (db, .ok r, writes && !inTxn)
    | .error e db =>
      -- undo the statement: its pages, and the schema as it was
      let p := db.pager.rollbackStmt
      let p := if inTxn then p else p.endTxn
      -- a RAISE's message is the error's
      let e := if e.msg.startsWith "\x01RAISE:" then { e with msg := ":".intercalate ((e.msg.splitOn ":").drop 2) } else e
      ({ db with pager := p, schema := sch0, trig := none, firing := [], inTemp := false, returned := none }, .error e, false)

end LSql

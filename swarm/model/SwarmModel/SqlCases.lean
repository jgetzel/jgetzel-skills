import Lean.Data.Json
import SwarmModel.SqlParse

/-! Random cases for each SQL statement of the Lua, with what `Sql.exec` says of them, for
../lua/test/sql_model_spec.lua to run on real sqlite through db.lua.
`lake env lean --run SwarmModel/SqlCases.lean <inventory> <n> <seed> <file>` (replay.sh): the inventory is
`luajit swarm/lua/test/sql_inventory.lua`'s output (site, tab, statement); `n` cases per statement.

The tables are the swarm's: db.SCHEMA, db.COLUMNS' migrations and cost.SCHEMA, run through `Sql.exec` from the
inventory's own text. A case fills the tables its statement names with 0 to 4 random rows (values by column
affinity, from small pools: the statement's own string literals, the same in capitals (for `like`) and
four other texts; and half the time the value
the statement compares that column with, so `kind='reap'` meets a `reap` and `ended is null` a NULL), and draws
each `?` mostly from one random row per table, the value of the column it is compared with (`id=? and owner=?`
meet a row), else from that column, any value the tables hold, NULL, small integers, a REAL and those texts. A migration runs on the tables without its column;
the `after` statements on a task table with one; a schema script on no tables or all of them. `begin`, `commit` and
`rollback` run in sequences: begin, a random statement, commit or rollback, and the errors (commit with no
transaction, begin twice).

`{"statements": [sql..], "cases": [{"sites", "tables": [{"name", "ddl", "rows", "seq"}], "steps": [{"sql", "params",
"script"}], "out": [{"err"} | {"names", "rows", "grps", "cut", "changes", "last"}], "final": [{"name", "info",
"rows", "seq"}]}]}`. A value is null, a number (INTEGER), {"r": x} (REAL) or a string (TEXT). -/

open Lean Swarm.Sql

abbrev G := StateM StdGen

def rnd (n : Nat) : G Nat := modifyGet fun g => randNat g 0 n
def pickL {α} [Inhabited α] (l : List α) : G α := return l.getD (← rnd (l.length - 1)) default

def valJson : Val → Json
  | .null => .null
  | .int i => toJson i
  | .real b => Json.mkObj [("r", toJson (Float.ofBits b))]
  | .text s => .str s

def rowsJson (rs : List (List Val)) : Json := Json.arr (rs.map fun r => Json.arr (r.map valJson).toArray).toArray

def texts : List String :=
  ["a", "b", "c", "A", "B", "Main Red: x", "OPEN", "1", "2", "1,2", "2,3", "open", "claimed", "blocked", "done", "dropped", "idle", "ended",
   "main red: x", "%", ""]

def ints : List Int := [0, 1, 2, 3, 5]

def literals (sql : String) : List String :=
  match lex (sql.length + 1) sql.toList 0 with
  | .ok ts => ts.filterMap fun t => match t.t with | .str s => some s | _ => none
  | .error _ => []

def randVal (pool : List String) : Aff → G Val
  | .text | .blob => do
    if (← rnd 6) == 0 then return .null
    return .text (← pickL pool)
  | _ => do
    match ← rnd 12 with
    | 0 | 1 | 2 | 3 => return .null
    | 4 => return .ofFloat 1.5
    | _ => return .int (← pickL ints)

/-- the column each `?` is compared with, if any: `id=?`, `owner is ?`, `id in (?,?)`, `question=?` in a SET -/
def paramCols (sql : String) : List (Option String × Option String) :=
  match lex (sql.length + 1) sql.toList 0 with
  | .error _ => []
  | .ok ts =>
    let skip (t : Tok) := match t with
      | .sym s => ["(", ",", "=", "!=", "<", ">", "<=", ">=", "=="].contains s
      | .q => true
      | .id w => ["in", "is", "not", "like"].contains (lower w)
      | _ => false
    let rec back : List Tok → Option String
      | [] => none
      | t :: r => if skip t then back r else match t with
        | .id w => if reserved.contains (lower w) || ["values", "limit", "coalesce"].contains (lower w) then none else some w
        | _ => none
    let op (i : Nat) : Option String := match (ts.getD (i - 1) default).t with | .sym s => some s | _ => none
    (List.range ts.length).filterMap fun i =>
      if (ts.getD i default).t == .q then some (back ((ts.take i).reverse.map (·.t)), op i) else none

/-- a `?`'s value: mostly one its column holds, so `name=?` meets a name; else one any column holds, or random -/
def randParam (pool : List String) (cells : List Val) (mine : List Val) : G Val := do
  if !mine.isEmpty && (← rnd 9) < 6 then return ← pickL mine
  if !cells.isEmpty && (← rnd 2) == 0 then return ← pickL cells
  match ← rnd 19 with
  | 0 | 1 | 2 => return .null
  | 3 => return .ofFloat (← pickL [1.5, -0.25])
  | 4 | 5 | 6 | 7 | 8 | 9 | 10 => return .int (← pickL ints)
  | _ => return .text (← pickL pool)

/-- what the statement compares columns with: `state='claimed'`, `state in ('open','claimed')`, `ended is null` -/
def hints (sql : String) : List (String × Val) :=
  match lex (sql.length + 1) sql.toList 0 with
  | .error _ => []
  | .ok ts =>
    let ts : List Tok := ts.map (·.t)
    (List.range ts.length).flatMap fun i =>
      match ts.drop i with
      | .id c :: .sym "=" :: .str v :: _ | .id c :: .sym "!=" :: .str v :: _ => [(c, .text v)]
      | .id c :: .id w :: .id nl :: _ => if lower w == "is" && lower nl == "null" then [(c, .null)] else []
      | .id c :: .id w :: .sym "(" :: r =>
        if lower w == "in" then (r.takeWhile (· != .sym ")")).filterMap fun t => match t with
          | .str v => some (c, .text v) | _ => none
        else []
      | _ => []

def randRows (pool : List String) (hs : List (String × Val)) (t : Table) : G Table := do
  let mut rows : List (List Val) := []
  for _ in [0:← rnd 4] do
    let mut r := []
    for c in t.cols do
      let v ← if t.rowid && t.pk == [c.name] then pure (Val.int ((← rnd 5) + 1 : Nat))
        else if t.pk.contains c.name then pure (Val.text (← pickL pool))
        else randVal pool c.aff
      let hs := hs.filter (·.1 == c.name)
      let v ← if !hs.isEmpty && !t.pk.contains c.name && (← rnd 1) == 0 then (·.2) <$> pickL hs else pure v
      r := r ++ [v]
    if t.clashes r |>.isEmpty then
      if !(rows.any fun x => (t.key x).isSome && t.key x == t.key r) then rows := rows ++ [r]
  let t := { t with rows }
  let k ← rnd 2
  return { t with seq := if t.autoinc then t.maxRowid + k else 0 }

def ddl (nm : String) (t : Table) : String :=
  let col (c : Col) :=
    c.name ++ (if c.ty.isEmpty then "" else " " ++ c.ty)
      ++ (if t.pk == [c.name] then " primary key" ++ (if t.autoinc then " autoincrement" else "") else "")
      ++ (c.dflt.map (" default " ++ ·)).getD ""
  let pk := if t.pk.length > 1 then [s!"primary key({",".intercalate t.pk})"] else []
  s!"create table {nm}({", ".intercalate (t.cols.map col ++ pk)})"

def tablesJson (db : DB) : Json :=
  Json.arr <| db.toArray.map fun (nm, t) => Json.mkObj
    [("name", nm), ("ddl", ddl nm t), ("rows", rowsJson t.rows), ("seq", toJson t.seq)]

def finalJson (db : DB) : Json :=
  Json.arr <| db.toArray.map fun (nm, t) => Json.mkObj
    [("name", nm), ("info", rowsJson (tableInfo t)), ("rows", rowsJson t.rows), ("seq", toJson t.seq)]

def isScript (sql : String) : Bool :=
  match parse sql with | .ok (ss, _) => ss.length > 1 || ss.any (fun s => match s with | .create .. | .createIndex => true | _ => false) | _ => false

/-- one step on the connection: Lean's answer, and the connection after -/
def step (c : Conn) (sql : String) (ps : List Val) : Json × Conn :=
  match parse sql with
  | .error e => (Json.mkObj [("err", s!"parse: {e}")], c)
  | .ok (ss, _) =>
    if isScript sql then
      match script c ss with
      | (c, some e) => (Json.mkObj [("err", e)], c)
      | (c, none) => (Json.mkObj [("names", Json.arr #[]), ("rows", Json.arr #[]), ("grps", Json.arr #[]),
          ("cut", false), ("changes", c.changes), ("last", toJson c.lastId)], c)
    else match ss with
    | [s] => match exec c s ps with
      | .ok (o, c) => (Json.mkObj [("names", toJson o.names), ("rows", rowsJson o.rows), ("grps", toJson o.grps),
          ("cut", o.cut), ("changes", c.changes), ("last", toJson c.lastId)], c)
      | .error e => (Json.mkObj [("err", e)], c)
    | _ => (Json.mkObj [("err", "not one statement")], c)

def mentions (sql nm : String) : Bool :=
  let ws := (sql.toList.splitBy (fun a b => idChar a == idChar b)).map String.ofList
  ws.contains nm

def nparams (sql : String) : Nat := match parse sql with | .ok (_, k) => k | .error _ => 0

def case (base : DB) (stmts : List String) (sites : String) (sql : String) : G Json := do
  -- a few texts, so rows and `?`s meet: the statement's literals and four others
  let pool := literals sql ++ (literals sql).map String.toUpper ++ (← (List.range 4).mapM fun _ => pickL texts)
  let parsed := parse sql
  let mut db := base
  -- the schema this statement meets
  match parsed with
  | .ok ([.addCol nm c], _) =>
    if let .ok t := lookup db nm then
      if let some i := t.idx c.name then db := db.set nm { t with cols := t.cols.eraseIdx i }
  | .ok (ss, _) =>
    if ss.any (fun s => match s with | .create .. => true | _ => false) && (← rnd 1) == 0 then db := []
  | _ => pure ()
  if mentions sql "after" then
    if let .ok t := lookup db "task" then
      if (t.idx "after").isNone then db := db.set "task" { t with cols := t.cols ++ [{ name := "after", ty := "text" }] }
  let tx := ["begin immediate", "commit", "rollback"].contains sql
  -- the statements of a step: this one, or a transaction around a random one
  let mut steps : List String := [sql]
  if tx then
    let dml := stmts.filter fun s => ["insert", "update", "delete"].any (s.startsWith ·)
    let other ← pickL dml
    steps ← match ← rnd 4 with
      | 0 => pure ["begin immediate", other, "commit"]
      | 1 => pure ["begin immediate", other, "rollback"]
      | 2 => pure ["begin immediate", "begin immediate", other]
      | _ => pure [sql, other]
    db := base
  let mentioned := (steps.flatMap fun s => db.filter (fun (nm, _) => mentions s nm)).map (·.1)
  let mut filled : DB := []
  for (nm, t) in db do
    let t ← if mentioned.contains nm then randRows (pool ++ steps.flatMap literals) (steps.flatMap hints) t else pure t
    filled := filled ++ [(nm, t)]
  let mut c : Conn := { db := filled }
  let cells := filled.flatMap (fun (_, t) => t.rows.flatten) |>.filter (· != .null)
  let mut stepsJ := #[]
  let mut outs := #[]
  for s in steps do
    let pc := paramCols s
    -- one row per table that the step's `?`s are mostly drawn from, so `id=? and owner=?` meets a row
    let anchors : List (Table × List Val) ← filled.mapM fun (_, t) => do pure (t, t.rows.getD (← rnd (t.rows.length - 1)) [])
    let ps ← (List.range (nparams s)).mapM fun i => do
      let (col, op) := pc.getD i (none, none)
      let anchored : List Val := match col with
        | some col => anchors.filterMap fun (t, r) => if r.isEmpty then none else (t.idx col).map (r.getD · .null)
        | none => []
      let mine : List Val := match col with
        | some col => filled.flatMap (fun (_, t) => match t.idx col with
            | some j => t.rows.map (·.getD j .null) | none => []) |>.filter (· != .null)
        | none => []
      -- `x<?` meets the row's x with a neighbour of it; `x!=?` isn't anchored
      if !anchored.isEmpty && op != some "!=" && (← rnd 9) < 7 then
        return match anchored.headD .null, op with
          | .int v, some "<" | .int v, some "<=" => .int (v + 1)
          | .int v, some ">" | .int v, some ">=" => .int (v - 1)
          | v, _ => v
      randParam (pool ++ literals s) cells mine
    stepsJ := stepsJ.push (Json.mkObj [("sql", s), ("params", Json.arr (ps.map valJson).toArray), ("script", isScript s)])
    let (o, c') := step c s ps
    outs := outs.push o
    c := c'
  if c.saved.isSome then
    stepsJ := stepsJ.push (Json.mkObj [("sql", "rollback"), ("params", Json.arr #[]), ("script", false)])
    let (o, c') := step c "rollback" []
    outs := outs.push o
    c := c'
  return Json.mkObj [("sites", sites), ("tables", tablesJson filled), ("steps", Json.arr stepsJ), ("out", Json.arr outs),
    ("final", finalJson c.db)]

def main (args : List String) : IO UInt32 := do
  let [inv, n, seed, file] := args | do
    IO.eprintln "usage: SqlCases.lean <inventory> <n> <seed> <file>"; return 1
  let lines := (← IO.FS.lines inv).toList.filter (· != "")
  let pairs := lines.map fun l => match l.splitOn "\t" with | s :: q :: _ => (s, q) | _ => ("", l)
  let mut bad := 0
  for (s, q) in pairs do
    if let .error e := parse q then IO.eprintln s!"{s}: {e}: {q}"; bad := bad + 1
  if bad > 0 then return 1
  -- the swarm's tables: the schema scripts, then the column migrations (an existing column's is refused)
  let mut c : Conn := { db := [] }
  for (_, q) in pairs do
    if let .ok (ss, _) := parse q then
      if ss.all (fun s => match s with | .create .. | .createIndex => true | _ => false) then c := (script c ss).1
  for (_, q) in pairs do
    if let .ok ([s@(.addCol ..)], _) := parse q then
      if let .ok (_, c') := exec c s [] then c := c'
  let stmts := pairs.map (·.2) |>.eraseDups
  let sites (q : String) := ",".intercalate (pairs.filter (·.2 == q) |>.map (·.1))
  let gen : G (List Json) := do
    let mut r := []
    for q in stmts do
      for _ in [0:n.toNat!] do r := r ++ [← case c.db stmts (sites q) q]
    return r
  let cases := gen.run' (mkStdGen seed.toNat!)
  IO.FS.writeFile file (Json.mkObj [("statements", toJson stmts), ("cases", Json.arr cases.toArray)]).compress
  IO.println s!"{stmts.length} statements, {cases.length} cases"
  return 0

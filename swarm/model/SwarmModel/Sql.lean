/-! The SQL swarm/lua/swarm hands sqlite, as a semantics: values with sqlite's storage classes and affinities, tables
as lists of rows, and `exec`, one statement on a connection (`Conn`: the tables, the transaction's snapshot,
`changes()` and `last_insert_rowid()`). Only the subset the Lua uses (`../lua/test/sql_inventory.lua` lists it;
`SqlParse.lean` reads it). Recursion runs on fuel, so `decide` evaluates it.

A statement is atomic: an error leaves the connection as it was (sqlite's default ABORT). A transaction (`begin
immediate` .. `commit`) is atomic too, and `rollback` restores the snapshot `begin` took; one connection, so
concurrency is #33's. `SqlCases.lean` runs each statement on random tables and `../lua/test/sql_model_spec.lua`
runs the same through db.lua on real sqlite: results, `changes()`, `last_insert_rowid()` and the tables after. -/

namespace Swarm.Sql

/-- a value: sqlite's storage classes but BLOB (the Lua never writes one); a REAL is its IEEE bits -/
inductive Val where
  | null | int (i : Int) | real (bits : UInt64) | text (s : String)
  deriving DecidableEq, Repr, Inhabited

def Val.ofFloat (f : Float) : Val := .real f.toBits

/-! ## Numbers in text -/

def digits (l : List Char) : List Char × List Char := (l.takeWhile Char.isDigit, l.dropWhile Char.isDigit)

def natOf (ds : List Char) : Nat := ds.foldl (fun n c => 10 * n + (c.toNat - '0'.toNat)) 0

def sign : List Char → Bool × List Char
  | '-' :: r => (true, r) | '+' :: r => (false, r) | r => (false, r)

def isSpace (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r'

/-- the decimal `i.f` as a float -/
def decimal (neg : Bool) (i f : List Char) : Float :=
  let x := Float.ofNat (natOf i) + Float.ofNat (natOf f) / Float.ofNat (10 ^ f.length)
  if neg then -x else x

def i64 (i : Int) : Bool := -2^63 ≤ i && i < 2^63

/-- text that is a number as a whole (spaces around it allowed): an integer, or a decimal with a `.`.
ponytail: no exponent (`1e3`); sqlite reads one, the swarm never writes one -/
def wholeNum (s : String) : Option Val :=
  let l := (s.toList.dropWhile isSpace).reverse.dropWhile isSpace |>.reverse
  let (neg, l) := sign l
  let (i, l) := digits l
  match l with
  | [] => if i.isEmpty then none else
      let n : Int := if neg then -(natOf i : Int) else natOf i
      if i64 n then some (.int n) else some (.ofFloat (decimal neg i []))
  | '.' :: r =>
      let (f, rest) := digits r
      if rest.isEmpty && !(i.isEmpty && f.isEmpty) then some (.ofFloat (decimal neg i f)) else none
  | _ => none

/-- the number a text starts with, as sqlite reads text in arithmetic, `cast` and a truth test: 0 if none -/
def prefixNum (s : String) : Val :=
  let (neg, l) := sign (s.toList.dropWhile isSpace)
  let (i, l) := digits l
  match l with
  | '.' :: r =>
      let (f, _) := digits r
      if f.isEmpty then .int (if neg then -(natOf i : Int) else natOf i) else .ofFloat (decimal neg i f)
  | _ => .int (if neg then -(natOf i : Int) else natOf i)

def Val.toFloat : Val → Float
  | .int i => Float.ofInt i | .real b => Float.ofBits b | _ => 0

/-- a REAL that is a whole number in range, as an INTEGER -/
def intIfWhole (f : Float) : Option Int :=
  if f.floor == f && f.abs < 9.2e18 then some f.toInt64.toInt else none

/-- sqlite's "%!.15g" of a REAL, for the values the swarm meets.
ponytail: exact only for a whole number below 1e15 or one with at most 15 decimals; anything else prints Lean's way -/
def realText (f : Float) : String :=
  match intIfWhole f with
  | some i => if f.abs < 1e15 then toString i ++ ".0" else toString f
  | none =>
    let neg := f < 0
    let a := f.abs
    let k := (List.range 15).find? (fun k => let x := a * Float.ofNat (10 ^ (k + 1)); x.floor == x)
    match k with
    | some k =>
      let n := (a * Float.ofNat (10 ^ (k + 1))).toUInt64.toNat
      let ds := toString n
      let ds := String.ofList (List.replicate (k + 2 - ds.length) '0') ++ ds
      let cut := ds.length - (k + 1)
      (if neg then "-" else "") ++ String.ofList (ds.toList.take cut) ++ "." ++ String.ofList (ds.toList.drop cut)
    | none => toString f

/-- a value as TEXT (`||`, `like`, lower) -/
def Val.str : Val → Option String
  | .null => none | .int i => some (toString i) | .real b => some (realText (Float.ofBits b)) | .text s => some s

/-- a value as a number (arithmetic, a truth test) -/
def Val.num : Val → Val
  | .text s => prefixNum s | v => v

/-- WHERE's reading of a value: NULL is unknown -/
def Val.truth : Val → Option Bool
  | .null => none
  | v => match v.num with
    | .int i => some (i != 0) | .real b => some (Float.ofBits b != 0) | _ => some false

def ofBool : Option Bool → Val
  | some true => .int 1 | some false => .int 0 | none => .null

/-! ## Affinity and comparison -/

inductive Aff where | int | text | blob | real | num
  deriving DecidableEq, Repr

def upperC (c : Char) : Char := if 'a' ≤ c && c ≤ 'z' then Char.ofNat (c.toNat - 32) else c

def upper (s : String) : String := String.ofList (s.toList.map upperC)

/-- a declared type's affinity (sqlite's five rules, in order). Over the characters, not String.toUpper, so the
kernel reduces it -/
def affOf (ty : String) : Aff :=
  let u := ty.toList.map upperC
  let has (w : String) := (List.range (u.length + 1)).any fun i => w.toList.isPrefixOf (u.drop i)
  if has "INT" then .int
  else if has "CHAR" || has "CLOB" || has "TEXT" then .text
  else if u.isEmpty || has "BLOB" then .blob
  else if has "REAL" || has "FLOA" || has "DOUB" then .real
  else .num

def Aff.numeric : Aff → Bool | .int | .real | .num => true | _ => false

/-- NUMERIC affinity: a text that is a number becomes one; a whole REAL becomes an INTEGER -/
def toNumeric : Val → Val
  | .text s => match wholeNum s with
    | some (.real b) => match intIfWhole (Float.ofBits b) with | some i => .int i | none => .real b
    | some v => v
    | none => .text s
  | .real b => match intIfWhole (Float.ofBits b) with | some i => .int i | none => .real b
  | v => v

/-- a value stored in a column of affinity `a` -/
def Aff.apply : Aff → Val → Val
  | .int, v | .num, v => toNumeric v
  | .real, v => match toNumeric v with | .int i => .ofFloat (Float.ofInt i) | w => w
  | .text, .int i => .text (toString i)
  | .text, .real b => .text (realText (Float.ofBits b))
  | _, v => v

def cmpF (a b : Float) : Ordering := if a < b then .lt else if a == b then .eq else .gt

/-- sqlite's order of values: NULL, numbers, text (BINARY: code points, which is UTF-8's byte order) -/
def cmp : Val → Val → Ordering
  | .null, .null => .eq | .null, _ => .lt | _, .null => .gt
  | .text a, .text b => compare a b
  | .text _, _ => .gt | _, .text _ => .lt
  | .int a, .int b => compare a b
  | a, b => cmpF a.toFloat b.toFloat

/-- the affinities sqlite applies to the operands of a comparison, given each operand's affinity (none: an
expression that isn't a column or a cast) -/
def coerce (aa ab : Option Aff) (x y : Val) : Val × Val :=
  let num (o : Option Aff) := o.any Aff.numeric
  let noAff (o : Option Aff) := o.all (· == .blob)
  if num aa && !num ab then (x, toNumeric y)
  else if num ab && !num aa then (toNumeric x, y)
  else if aa == some .text && noAff ab then (x, Aff.text.apply y)
  else if ab == some .text && noAff aa then (Aff.text.apply x, y)
  else (x, y)

/-! ## `like` -/

def lowerC (c : Char) : Char := if 'A' ≤ c && c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c

/-- `like` with `%` and `_`, no ESCAPE; ASCII letters match either case -/
def likeM : List Char → List Char → Bool
  | [], s => s.isEmpty
  | '%' :: p, s => (List.range (s.length + 1)).any (fun k => likeM p (s.drop k))
  | '_' :: p, s => !s.isEmpty && likeM p s.tail
  | c :: p, s => match s with
    | d :: s => lowerC c == lowerC d && likeM p s
    | [] => false

/-! ## Schema, tables, the connection -/

/-- a column as declared: its type's text and its default's (`default 0`), and that value -/
structure Col where
  name : String
  ty : String
  dflt : Option String := none
  dfltV : Val := .null
  deriving DecidableEq, Repr, Inhabited

def Col.aff (c : Col) : Aff := affOf c.ty

structure Table where
  cols : List Col
  /-- the primary key's columns -/
  pk : List String := []
  /-- the primary key is one `integer primary key` column: it is the rowid -/
  rowid : Bool := false
  autoinc : Bool := false
  rows : List (List Val) := []
  /-- sqlite_sequence's row (0 if none), for an `autoincrement` table -/
  seq : Int := 0
  deriving DecidableEq, Repr, Inhabited

abbrev DB := List (String × Table)

structure Conn where
  db : DB
  /-- the tables when `begin` ran, while a transaction is open -/
  saved : Option DB := none
  changes : Nat := 0
  /-- last_insert_rowid(); none after an insert into a table whose rowid is hidden (not modelled) -/
  lastId : Option Int := some 0
  deriving Repr, Inhabited

def Table.idx (t : Table) (c : String) : Option Nat := t.cols.findIdx? (·.name == c)

def lookup (db : DB) (t : String) : Except String Table :=
  match db.find? (·.1 == t) with
  | some (_, x) => .ok x
  | none => .error s!"no such table: {t}"

def DB.set (db : DB) (t : String) (x : Table) : DB :=
  if db.any (·.1 == t) then db.map (fun p => if p.1 == t then (t, x) else p) else db ++ [(t, x)]

/-! ## Syntax -/

inductive BinOp where
  | eq | ne | lt | le | gt | ge | is | isNot | and | or | concat | add | sub | like
  deriving DecidableEq, Repr

mutual
inductive Expr where
  | lit (v : Val)
  /-- the i-th `?`, from 0 -/
  | param (i : Nat)
  | col (q : Option String) (c : String)
  | bin (op : BinOp) (a b : Expr)
  | not (a : Expr)
  | neg (a : Expr)
  | inList (neg : Bool) (a : Expr) (l : List Expr)
  | inSel (neg : Bool) (a : Expr) (s : Select)
  | exists (s : Select)
  | sub (s : Select)
  /-- `case when c₁ then v₁ .. else e end` -/
  | case (cs vs : List Expr) (els : Expr)
  | call (f : String) (args : List Expr)
  | countStar
  | cast (a : Expr) (ty : String)
  deriving Repr, Inhabited

/-- `select [distinct] cols [from t [a] [join t2 [a2] on e]] [where] [group by] [order by] [limit]`; `agg`: a
`max(x)` or `count(*)` among its columns or order (the parser's flag) -/
inductive Select where
  | mk (distinct agg : Bool) (cols : List SelCol) (src : Option Src) (where_ : Option Expr) (group : List Expr)
      (order : List OrderBy) (limit : Option Expr)
  deriving Repr, Inhabited

/-- a result column: `*`, `a.*`, or an expression with its name (the alias, else the column's, else its text) -/
inductive SelCol where
  | star (q : Option String)
  | expr (e : Expr) (name : String)
  deriving Repr, Inhabited

inductive OrderBy where
  | mk (e : Expr) (desc : Bool)
  deriving Repr, Inhabited

/-- a table and its alias, and an inner join's -/
inductive Src where
  | mk (t a : String) (join : Option Join)
  deriving Repr, Inhabited

inductive Join where
  | mk (t a : String) (on : Expr)
  deriving Repr, Inhabited
end

inductive OnConflict where | abort | ignore | replace
  deriving DecidableEq, Repr

inductive Stmt where
  | select (s : Select)
  /-- `select .. union all select ..`: both's rows, in no defined order (no ORDER BY or LIMIT on the compound) -/
  | unionAll (a b : Select)
  /-- `insert [or ..] into t [(cols)] values (..),.. | select ..  [on conflict(cols) do update set ..] [returning ..]` -/
  | insert (or_ : OnConflict) (t : String) (cols : Option (List String)) (vals : List (List Expr)) (sel : Option Select)
      (upsert : Option (List String × List (String × Expr))) (ret : List SelCol)
  | update (t : String) (sets : List (String × Expr)) (where_ : Option Expr)
  | delete (t : String) (where_ : Option Expr)
  /-- `create table if not exists t(cols, [primary key(..)])` -/
  | create (t : String) (cols : List Col) (pk : List String) (rowid autoinc : Bool)
  | createIndex
  | addCol (t : String) (c : Col)
  | dropCol (t c : String)
  | tableInfo (t : String)
  | journal (mode : String)
  | begin | commit | rollback
  deriving Repr, Inhabited

/-! ## Evaluation -/

/-- one table's row in scope: its alias, columns and values -/
structure Frame where
  alias : String
  cols : List Col
  vals : List Val
  deriving Repr, Inhabited

structure Ctx where
  params : List Val
  /-- the rows in scope, innermost first -/
  frames : List Frame
  /-- the group's rows, while computing an aggregate select's columns -/
  grp : Option (List (List Frame)) := none

/-- a result: column names, rows, each row's tie group (rows of one group are in no defined order: the same ORDER
BY key, or no ORDER BY), and whether LIMIT cut a group (then which of its rows come out is not defined either) -/
structure Out where
  names : List String := []
  rows : List (List Val) := []
  grps : List Nat := []
  cut : Bool := false
  deriving Repr, Inhabited

def find (fs : List Frame) (q : Option String) (c : String) : Option (Val × Aff) :=
  fs.findSome? fun f =>
    if q.all (· == f.alias) then
      match f.cols.findIdx? (·.name == c) with
      | some i => some (f.vals.getD i .null, (f.cols.getD i default).aff)
      | none => none
    else none

/-- an expression's affinity: a column's, a cast's type's, else none -/
def exprAff (fs : List Frame) : Expr → Option Aff
  | .col q c => (find fs q c).map (·.2)
  | .cast _ ty => some (affOf ty)
  | _ => none

def compareOp (op : BinOp) (x y : Val) : Val :=
  match op with
  | .is => ofBool (some (cmp x y == .eq))
  | .isNot => ofBool (some (cmp x y != .eq))
  | _ =>
    if x == .null || y == .null then .null else
    let o := cmp x y
    ofBool <| some <| match op with
      | .eq => o == .eq | .ne => o != .eq | .lt => o == .lt | .le => o != .gt | .gt => o == .gt | .ge => o != .lt
      | _ => false

def arith (op : BinOp) (x y : Val) : Val :=
  match x.num, y.num with
  | .null, _ | _, .null => .null
  | .int a, .int b => .int (if op == .add then a + b else a - b)
  | a, b => .ofFloat (if op == .add then a.toFloat + b.toFloat else a.toFloat - b.toFloat)

def castTo (ty : String) (v : Val) : Except String Val :=
  match affOf ty, v with
  | _, .null => .ok .null
  | .int, .int i => .ok (.int i)
  | .int, .real b => .ok (.int (Float.ofBits b).toInt64.toInt)
  | .int, .text s => .ok (match prefixNum s with | .real b => .int (Float.ofBits b).toInt64.toInt | w => w)
  | _, _ => .error s!"cast to {ty}: not modelled"

def maxV (vs : List Val) : Val :=
  vs.foldl (fun m v => if v == .null then m else if m == .null || cmp v m == .gt then v else m) .null

/-- group rows by their keys (`=` with NULLs together), in order of first appearance -/
def groupBy (ks : List (List Val × List Frame)) : List (List (List Frame)) :=
  let eqk (a b : List Val) := a.length == b.length && (a.zip b).all (fun (x, y) => cmp x y == .eq)
  let gs := ks.foldl (fun (gs : List (List Val × List (List Frame))) (k, r) =>
    if gs.any (eqk ·.1 k) then gs.map (fun g => if eqk g.1 k then (g.1, g.2 ++ [r]) else g) else gs ++ [(k, [r])]) []
  gs.map (·.2)

def keyCmp (ds : List Bool) (a b : List Val) : Ordering :=
  ((ds.zip (a.zip b)).find? (fun (_, x, y) => cmp x y != .eq)).map (fun (d, x, y) =>
    if d then (cmp y x) else cmp x y) |>.getD .eq

/-- tie groups of consecutive rows with equal keys -/
def tieGroups (ordered : Bool) (ks : List (List Val)) : List Nat :=
  if !ordered then ks.map (fun _ => 0) else
  (ks.foldl (fun (acc : List Nat × Option (List Val) × Nat) k =>
    let (out, prev, g) := acc
    match prev with
    | none => (out ++ [0], some k, 0)
    | some p => if keyCmp (k.map fun _ => false) p k == .eq then (out ++ [g], some k, g) else (out ++ [g + 1], some k, g + 1)
    ) ([], none, 0)).1

def dedup (rs : List (List Val)) : List (List Val) :=
  rs.foldl (fun acc r => if acc.contains r then acc else acc ++ [r]) []

def starCols (fs : List Frame) (q : Option String) : List (String × Val) :=
  (fs.filter (fun f => q.all (· == f.alias))).flatMap (fun f => (f.cols.zip f.vals).map (fun (c, v) => (c.name, v)))

/-- `x [not] in (ys)`, each pair already coerced -/
def inResult (ng : Bool) (x : Val) (ps : List (Val × Val)) : Val :=
  if x == .null then (if ps.isEmpty then ofBool (some ng) else .null) else
  if ps.any (fun (a, b) => b != .null && cmp a b == .eq) then ofBool (some !ng)
  else if ps.any (fun (_, b) => b == .null) then .null else ofBool (some ng)

mutual
def eval : Nat → DB → Ctx → Expr → Except String Val
  | 0, _, _, _ => .error "out of fuel"
  | n + 1, db, cx, e => match e with
    | .lit v => .ok v
    | .param i => .ok (cx.params.getD i .null)
    | .col q c => match find cx.frames q c with
      | some (v, _) => .ok v
      | none => .error s!"no such column: {q.getD ""}{if q.isSome then "." else ""}{c}"
    | .bin op a b => do
      let x ← eval n db cx a
      match op with
      | .and => match x.truth with
        | some false => .ok (.int 0)
        | t => do let y ← eval n db cx b; .ok <| match t, y.truth with
          | _, some false => .int 0 | some true, some true => .int 1 | _, _ => .null
      | .or => match x.truth with
        | some true => .ok (.int 1)
        | t => do let y ← eval n db cx b; .ok <| match t, y.truth with
          | _, some true => .int 1 | some false, some false => .int 0 | _, _ => .null
      | _ => do
        let y ← eval n db cx b
        match op with
        | .concat => .ok (match x.str, y.str with | some s, some t => .text (s ++ t) | _, _ => .null)
        | .add | .sub => .ok (arith op x y)
        | .like => .ok (match y.str, x.str with
          | some p, some s => ofBool (some (likeM p.toList s.toList)) | _, _ => .null)
        | _ =>
          let (x, y) := coerce (exprAff cx.frames a) (exprAff cx.frames b) x y
          .ok (compareOp op x y)
    | .not a => do let x ← eval n db cx a; .ok (ofBool (x.truth.map (!·)))
    | .neg a => do let x ← eval n db cx a; .ok (arith .sub (.int 0) x)
    | .inList ng a l => do
      let x ← eval n db cx a
      let ys ← l.mapM (eval n db cx)
      let aa := exprAff cx.frames a
      .ok (inResult ng x (ys.map fun y => (coerce aa none x y)))
    | .inSel ng a s => do
      let x ← eval n db cx a
      let o ← select n db { cx with grp := none } s
      let aa := exprAff cx.frames a
      .ok (inResult ng x (o.rows.map fun r => coerce aa none x (r.headD .null)))
    | .exists s => do
      let o ← select n db { cx with grp := none } s
      .ok (ofBool (some !o.rows.isEmpty))
    | .sub s => do
      let o ← select n db { cx with grp := none } s
      .ok ((o.rows.headD []).headD .null)
    | .case cs vs els => caseOf n db cx cs vs els
    | .call f args => match f, args, cx.grp with
      | "max", [a], some rs => do
        let vs ← rs.mapM (fun fr => eval n db { cx with frames := fr ++ cx.frames, grp := none } a)
        .ok (maxV vs)
      | "max", [_], none => .error "misuse of aggregate function max()"
      | "coalesce", _ :: _ :: _, _ => coalesce n db cx args
      | "lower", [a], _ => do
        let x ← eval n db cx a
        .ok (match x.str with | some s => .text (String.ofList (s.toList.map lowerC)) | none => .null)
      | _, _, _ => .error s!"function {f}: not modelled"
    | .countStar => match cx.grp with
      | some rs => .ok (.int rs.length)
      | none => .error "misuse of aggregate function count()"
    | .cast a ty => do let x ← eval n db cx a; castTo ty x

/-- a WHERE or ON clause holds of the row in scope. sqlite splits it into its AND-terms and skips the row at the
first that isn't true, NULL included: a term after it isn't evaluated, so can't fail (`limit ?` on a text) -/
def test : Nat → DB → Ctx → Expr → Except String Bool
  | 0, _, _, _ => .error "out of fuel"
  | n + 1, db, cx, .bin .and a b => do if ← test n db cx a then test n db cx b else .ok false
  | n + 1, db, cx, e => do let v ← eval n db cx e; .ok (v.truth == some true)

def caseOf : Nat → DB → Ctx → List Expr → List Expr → Expr → Except String Val
  | 0, _, _, _, _, _ => .error "out of fuel"
  | n + 1, db, cx, c :: cs, v :: vs, els => do
    let x ← eval n db cx c
    if x.truth == some true then eval n db cx v else caseOf n db cx cs vs els
  | n + 1, db, cx, _, _, els => eval n db cx els

def coalesce : Nat → DB → Ctx → List Expr → Except String Val
  | 0, _, _, _ => .error "out of fuel"
  | _ + 1, _, _, [] => .ok .null
  | n + 1, db, cx, a :: r => do
    let x ← eval n db cx a
    if x == .null then coalesce n db cx r else .ok x

/-- the rows of the FROM clause, each the frames of its tables -/
def source : Nat → DB → Ctx → Option Src → Except String (List (List Frame))
  | 0, _, _, _ => .error "out of fuel"
  | _ + 1, _, _, none => .ok [[]]
  | n + 1, db, cx, some (.mk t a j) => do
    let x ← lookup db t
    let rs := x.rows.map fun r => [Frame.mk a x.cols r]
    match j with
    | none => .ok rs
    | some (.mk t2 a2 on) => do
      let y ← lookup db t2
      let pairs := rs.flatMap fun r => y.rows.map fun r2 => r ++ [Frame.mk a2 y.cols r2]
      pairs.filterM fun fr => test n db { cx with frames := fr ++ cx.frames } on

/-- one output row's columns: names and values -/
def row : Nat → DB → Ctx → List Frame → List SelCol → Except String (List (String × Val))
  | 0, _, _, _, _ => .error "out of fuel"
  | _ + 1, _, _, _, [] => .ok []
  | n + 1, db, cx, fr, c :: cs => do
    let here ← match c with
      | .star q => .ok (starCols fr q)
      | .expr e nm => do let v ← eval n db cx e; .ok [(nm, v)]
    let rest ← row n db cx fr cs
    .ok (here ++ rest)

def select : Nat → DB → Ctx → Select → Except String Out
  | 0, _, _, _ => .error "out of fuel"
  | n + 1, db, cx, .mk distinct agg cols src where_ group order limit => do
    let rows ← source n db cx src
    let rows ← rows.filterM fun fr => match where_ with
      | none => .ok true
      | some w => test n db { cx with frames := fr ++ cx.frames, grp := none } w
    -- each output row: its scope frames and, when aggregating, its group
    let units : List (List Frame × Option (List (List Frame))) ←
      if agg || !group.isEmpty then do
        let ks ← rows.mapM fun fr => do
          let k ← group.mapM (eval n db { cx with frames := fr ++ cx.frames, grp := none })
          .ok (k, fr)
        let gs := if group.isEmpty then [rows] else groupBy ks
        let nullFr : List Frame := match src with
          | some (.mk t a _) => match lookup db t with
            | .ok x => [Frame.mk a x.cols (x.cols.map fun _ => .null)] | _ => []
          | none => []
        .ok (gs.map fun g => (g.headD nullFr, some g))
      else .ok (rows.map fun fr => (fr, none))
    let out ← units.mapM fun (fr, g) => do
      let c := { cx with frames := fr ++ cx.frames, grp := g }
      let r ← row n db c fr cols
      let k ← order.mapM fun (.mk e _) => eval n db c e
      .ok (r, k)
    let names := (out.headD ([], [])).1.map (·.1)
    let names ← if out.isEmpty then (do
        let fr ← match src with
          | some (.mk t a j) => do
            let x ← lookup db t
            let f := [Frame.mk a x.cols (x.cols.map fun _ => .null)]
            match j with
            | some (.mk t2 a2 _) => do let y ← lookup db t2; .ok (f ++ [Frame.mk a2 y.cols (y.cols.map fun _ => .null)])
            | none => .ok f
          | none => .ok []
        .ok (cols.flatMap fun c => match c with
          | .star q => (starCols fr q).map (·.1)
          | .expr _ nm => [nm]))
      else .ok names
    let out := out.map fun (r, k) => (r.map (·.2), k)
    let out := if distinct then (dedup (out.map (·.1))).map (fun r => (r, [])) else out
    let ds := order.map fun (.mk _ d) => d
    let sorted := out.mergeSort (fun a b => keyCmp ds a.2 b.2 != .gt)
    let ordered := !order.isEmpty
    let (kept, cut) ← match limit with
      | none => .ok (sorted, false)
      | some l => do
        let v ← eval n db { cx with grp := none } l
        match toNumeric v with
        | .int i =>
          if i < 0 then .ok (sorted, false) else
          let k := i.toNat
          let cut := sorted.length > k && k > 0 &&
            (!ordered || keyCmp ds (sorted.getD (k - 1) ([], [])).2 (sorted.getD k ([], [])).2 == .eq)
          .ok (sorted.take k, cut)
        | _ => .error "datatype mismatch"
    .ok { names, rows := kept.map (·.1), grps := tieGroups ordered (kept.map (·.2)), cut }
end


/-! ## Statements -/

/-- recursion depth for an expression or select: the swarm's nest a few levels -/
def fuel : Nat := 64

def evalTop (db : DB) (ps : List Val) (fs : List Frame) (e : Expr) : Except String Val :=
  eval fuel db { params := ps, frames := fs } e

def Table.pkIdx (t : Table) : List Nat := t.pk.map fun c => (t.idx c).getD 0

/-- a row's key, if the table has one and no part of it is NULL (sqlite lets NULLs into a non-rowid key, each distinct) -/
def Table.key (t : Table) (r : List Val) : Option (List Val) :=
  if t.pk.isEmpty then none else
  let k := t.pkIdx.map fun i => r.getD i .null
  if k.contains .null then none else some k

def sameKey (a b : List Val) : Bool := a.length == b.length && (a.zip b).all fun (x, y) => cmp x y == .eq

def Table.clashes (t : Table) (r : List Val) : List (List Val) :=
  match t.key r with
  | none => []
  | some k => t.rows.filter fun x => (t.key x).any (sameKey k)

/-- no two rows share a key -/
def uniqueRows (t : Table) : List (List Val) → Bool
  | [] => true
  | r :: rs => (match t.key r with | none => true | some k => !rs.any fun x => (t.key x).any (sameKey k)) && uniqueRows t rs

def Table.maxRowid (t : Table) : Int :=
  match t.pkIdx with
  | [i] => t.rows.foldl (fun m r => match r.getD i .null with | .int v => max m v | _ => m) 0
  | _ => 0

/-- a rowid column holds an INTEGER, or NULL for the next rowid -/
def Table.rowidOk (t : Table) (r : List Val) : Except String (List Val) :=
  if !t.rowid then .ok r else
  let i := t.pkIdx.headD 0
  match r.getD i .null with
  | .null => .ok (r.set i (.int ((if t.autoinc then max t.seq t.maxRowid else t.maxRowid) + 1)))
  | .int _ => .ok r
  | _ => .error "datatype mismatch"

def Table.rowidOf (t : Table) (r : List Val) : Option Int :=
  if t.rowid then match r.getD (t.pkIdx.headD 0) .null with | .int i => some i | _ => none else none

def Table.bump (t : Table) (r : List Val) : Table :=
  if t.autoinc then match t.rowidOf r with | some i => { t with seq := max t.seq i } | none => t else t

def Table.uniqueErr (t : Table) (nm : String) : String :=
  s!"UNIQUE constraint failed: {", ".intercalate (t.pk.map fun c => nm ++ "." ++ c)}"

/-- a new row from the named columns' values: affinities applied, defaults for the rest -/
def Table.fresh (t : Table) (nm : String) (cols : List String) (vs : List Val) : Except String (List Val) := do
  if let some c := cols.find? (fun c => (t.idx c).isNone) then .error s!"table {nm} has no column named {c}"
  if cols.length != vs.length then .error s!"{vs.length} values for {cols.length} columns"
  t.rowidOk <| t.cols.map fun c => match cols.idxOf? c.name with
    | some j => c.aff.apply (vs.getD j .null)
    | none => c.dfltV

/-- set columns of a row from expressions over `fs` (the row, and `excluded` in an upsert) -/
def Table.assign (t : Table) (db : DB) (ps : List Val) (fs : List Frame) (sets : List (String × Expr))
    (r : List Val) : Except String (List Val) := do
  let vs ← sets.mapM fun (c, e) => do
    let some i := t.idx c | .error s!"no such column: {c}"
    let v ← evalTop db ps fs e
    .ok (i, (t.cols.getD i default).aff.apply v)
  let r' := vs.foldl (fun r (i, v) => r.set i v) r
  if t.rowid then match r'.getD (t.pkIdx.headD 0) .null with
    | .int _ => .ok r' | _ => .error "datatype mismatch"
  else .ok r'

/-- one row into a table: the table after, the row as stored (none if ignored), and whether it was a new row -/
def Table.put (t : Table) (nm : String) (db : DB) (ps : List Val) (or_ : OnConflict)
    (up : Option (List String × List (String × Expr))) (r : List Val) : Except String (Table × Option (List Val) × Bool) := do
  let cs := t.clashes r
  if cs.isEmpty then return ({ (t.bump r) with rows := t.rows ++ [r] }, some r, true)
  match up with
  | some (target, sets) =>
    if target != t.pk then throw "ON CONFLICT clause does not match any PRIMARY KEY or UNIQUE constraint"
    let old := cs.headD []
    let new ← t.assign db ps [Frame.mk nm t.cols old, Frame.mk "excluded" t.cols r] sets old
    let rows := t.rows.map fun x => if x == old then new else x
    if !uniqueRows t rows then throw (t.uniqueErr nm)
    return ({ t with rows }, some new, false)
  | none => match or_ with
    | .abort => throw (t.uniqueErr nm)
    | .ignore => return (t, none, false)
    | .replace => return ({ (t.bump r) with rows := t.rows.filter (fun x => !cs.contains x) ++ [r] }, some r, true)

/-- table_info's type: as declared, but sqlite (3.37 on) writes the standard names in capitals -/
def infoType (ty : String) : String :=
  if ["INT", "INTEGER", "TEXT", "REAL", "BLOB", "ANY"].contains (upper ty) then upper ty else ty

def tableInfo (t : Table) : List (List Val) :=
  (List.range t.cols.length).zip t.cols |>.map fun (i, c) =>
    [.int i, .text c.name, .text (infoType c.ty), .int 0, (c.dflt.map Val.text).getD .null,
     .int (match t.pk.idxOf? c.name with | some j => j + 1 | none => 0)]

def retCols (db : DB) (ps : List Val) (fs : List Frame) (ret : List SelCol) : Except String (List String × List Val) := do
  let r ← row fuel db { params := ps, frames := fs } fs ret
  .ok (r.map (·.1), r.map (·.2))

/-! ## Names

sqlite resolves every table and column name when it prepares a statement, before any row: a name that isn't there
fails the statement even where no row would reach it (`set deps=after where deps is null` on a table with no
`after` and no row with a NULL `deps`). A scope is the tables in reach, innermost first: alias and columns. -/

abbrev Scope := List (String × List Col)

def hasCol (sc : Scope) (q : Option String) (c : String) : Bool :=
  sc.any fun (a, cs) => q.all (· == a) && cs.any (·.name == c)

def tableCols (db : DB) (t : String) : Except String (List Col) := (lookup db t).map (·.cols)

mutual
def chkE : Nat → DB → Scope → Expr → Except String Unit
  | 0, _, _, _ => .error "out of fuel"
  | n + 1, db, sc, e => match e with
    | .col q c => if hasCol sc q c then .ok () else
        .error s!"no such column: {q.getD ""}{if q.isSome then "." else ""}{c}"
    | .bin _ a b => do chkE n db sc a; chkE n db sc b
    | .not a | .neg a | .cast a _ => chkE n db sc a
    | .inList _ a l => do chkE n db sc a; chkL n db sc l
    | .inSel _ a q => do chkE n db sc a; chkS n db sc q
    | .exists q | .sub q => chkS n db sc q
    | .case cs vs els => do chkL n db sc cs; chkL n db sc vs; chkE n db sc els
    | .call _ args => chkL n db sc args
    | _ => .ok ()

def chkL : Nat → DB → Scope → List Expr → Except String Unit
  | 0, _, _, _ => .error "out of fuel"
  | _ + 1, _, _, [] => .ok ()
  | n + 1, db, sc, e :: r => do chkE n db sc e; chkL n db sc r

def chkS : Nat → DB → Scope → Select → Except String Unit
  | 0, _, _, _ => .error "out of fuel"
  | n + 1, db, sc, .mk _ _ cols src w g o l => do
    let here ← match src with
      | none => pure []
      | some (.mk t a j) => do
        let x ← tableCols db t
        match j with
        | none => pure [(a, x)]
        | some (.mk t2 a2 on) => do
          let y ← tableCols db t2
          chkE n db ([(a, x), (a2, y)] ++ sc) on
          pure [(a, x), (a2, y)]
    let sc' := here ++ sc
    chkL n db sc' (cols.filterMap fun c => match c with | .expr e _ => some e | .star _ => none)
    chkL n db sc' (w.toList ++ g ++ o.map (fun (.mk e _) => e))
    chkL n db sc l.toList
end

def selExprs (cs : List SelCol) : List Expr := cs.filterMap fun c => match c with | .expr e _ => some e | .star _ => none

def setsOk (nm : String) (x : List Col) (sets : List (String × Expr)) : Except String Unit :=
  match sets.find? (fun (c, _) => !x.any (·.name == c)) with
  | some (c, _) => .error s!"table {nm} has no column named {c}"
  | none => .ok ()

/-- every name the statement uses is there, as sqlite's prepare checks -/
def Stmt.names (db : DB) : Stmt → Except String Unit
  | .select q => chkS fuel db [] q
  | .unionAll a b => do chkS fuel db [] a; chkS fuel db [] b
  | .insert _ nm cols vals sel up ret => do
    let x ← tableCols db nm
    setsOk nm x ((cols.getD []).map fun c => (c, .lit .null))
    chkL fuel db [] vals.flatten
    if let some q := sel then chkS fuel db [] q
    if let some (_, sets) := up then
      setsOk nm x sets
      chkL fuel db [(nm, x), ("excluded", x)] (sets.map (·.2))
    chkL fuel db [(nm, x)] (selExprs ret)
  | .update nm sets w => do
    let x ← tableCols db nm
    setsOk nm x sets
    chkL fuel db [(nm, x)] (sets.map (·.2) ++ w.toList)
  | .delete nm w => do
    let x ← tableCols db nm
    chkL fuel db [(nm, x)] w.toList
  | _ => .ok ()

/-- one statement on a connection with its `?` values: the result and the connection after, or an error and the
connection unchanged -/
def exec (c : Conn) (s : Stmt) (ps : List Val) : Except String (Out × Conn) := do
  let db := c.db
  s.names db
  match s with
  | .select q =>
    let o ← select fuel db { params := ps, frames := [] } q
    return (o, c)
  | .unionAll a b =>
    let x ← select fuel db { params := ps, frames := [] } a
    let y ← select fuel db { params := ps, frames := [] } b
    if x.names.length != y.names.length then throw "SELECTs to the left and right of UNION ALL do not have the same number of result columns"
    let rows := x.rows ++ y.rows
    return ({ names := x.names, rows, grps := rows.map fun _ => 0 }, c)
  | .insert or_ nm cols vals sel up ret =>
    let t ← lookup db nm
    let cols := cols.getD (t.cols.map (·.name))
    let srcRows ← match sel with
      | some q => do let o ← select fuel db { params := ps, frames := [] } q; pure o.rows
      | none => vals.mapM fun es => es.mapM (evalTop db ps [])
    let (t, n, last, out) ← srcRows.foldlM (init := (t, 0, c.lastId, ([] : List (List Val)))) fun (t, n, last, out) vs => do
      let r ← t.fresh nm cols vs
      let (t, stored, new) ← t.put nm db ps or_ up r
      let last := if new then t.rowidOf r else last
      match stored with
      | some r => do
        let (_, rv) ← retCols db ps [Frame.mk nm t.cols r] ret
        pure (t, n + 1, last, out ++ (if ret.isEmpty then [] else [rv]))
      | none => pure (t, n, last, out)
    let names ← if ret.isEmpty then pure [] else
      (retCols db ps [Frame.mk nm t.cols (t.cols.map fun _ => .null)] ret).map (·.1)
    return ({ names, rows := out, grps := out.map fun _ => 0 },
      { c with db := db.set nm t, changes := n, lastId := last })
  | .update nm sets w =>
    let t ← lookup db nm
    let rs ← t.rows.mapM fun r => do
      let fs := [Frame.mk nm t.cols r]
      let hit ← match w with
        | none => pure true
        | some w => test fuel db { params := ps, frames := fs } w
      if hit then do let r' ← t.assign db ps fs sets r; pure (r', true) else pure (r, false)
    let rows := rs.map (·.1)
    if !uniqueRows t rows then throw (t.uniqueErr nm)
    return ({}, { c with db := db.set nm { t with rows }, changes := (rs.filter (·.2)).length })
  | .delete nm w =>
    let t ← lookup db nm
    let keep ← t.rows.mapM fun r => match w with
      | none => pure false
      | some w => do pure !(← test fuel db { params := ps, frames := [Frame.mk nm t.cols r] } w)
    let rows := (t.rows.zip keep).filter (·.2) |>.map (·.1)
    return ({}, { c with db := db.set nm { t with rows }, changes := t.rows.length - rows.length })
  | .create nm cols pk rowid autoinc =>
    if db.any (·.1 == nm) then return ({}, c)
    return ({}, { c with db := db.set nm { cols, pk, rowid, autoinc } })
  | .createIndex => return ({}, c)
  | .addCol nm col =>
    let t ← lookup db nm
    if (t.idx col.name).isSome then throw s!"duplicate column name: {col.name}"
    return ({}, { c with db := db.set nm { t with cols := t.cols ++ [col], rows := t.rows.map (· ++ [col.dfltV]) } })
  | .dropCol nm col =>
    let t ← lookup db nm
    let some i := t.idx col | throw s!"no such column: \"{col}\""
    if t.pk.contains col then throw s!"cannot drop PRIMARY KEY column: \"{col}\""
    return ({}, { c with db := db.set nm { t with cols := t.cols.eraseIdx i, rows := t.rows.map (·.eraseIdx i) } })
  | .tableInfo nm =>
    let rows := match lookup db nm with | .ok t => tableInfo t | .error _ => []
    return ({ names := ["cid", "name", "type", "notnull", "dflt_value", "pk"], rows, grps := rows.map fun _ => 0 }, c)
  | .journal m => return ({ names := ["journal_mode"], rows := [[.text m]], grps := [0] }, c)
  | .begin =>
    if c.saved.isSome then throw "cannot start a transaction within a transaction"
    return ({}, { c with saved := some db })
  | .commit =>
    if c.saved.isNone then throw "cannot commit - no transaction is active"
    return ({}, { c with saved := none })
  | .rollback =>
    match c.saved with
    | none => throw "cannot rollback - no transaction is active"
    | some d => return ({}, { c with db := d, saved := none })

/-- a script (db:script, sqlite3_exec): its statements in turn, stopping at the first error, which keeps the ones
before it -/
def script (c : Conn) : List Stmt → Conn × Option String
  | [] => (c, none)
  | s :: r => match exec c s [] with
    | .ok (_, c) => script c r
    | .error e => (c, some e)

end Swarm.Sql

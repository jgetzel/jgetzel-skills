import LSql.Plan
import LSql.Pragma
import LSql.Json
/-! Compiling the AST: name resolution (resolve.c), comparison affinity and collation (expr.c sqlite3CompareAffinity,
sqlite3ExprCollSeq), aggregate collection, and access-path choice per table (where.c, much reduced). Recursion is bounded
by `fuel` (an expression or query nesting depth). -/
namespace LSql

structure SrcInfo where
  name : String
  cols : Array String
  affs : Array Aff
  colls : Array Collation
  base : Nat
  rowid : Option Nat
  /-- columns USING merged into an earlier source's: not seen by `*` or by unqualified names -/
  hidden : Array Bool
  /-- the slots it takes (0: its columns, and its rowid's when it has one) -/
  width : Nat := 0
  /-- json_each / json_tree: its `value` column (slot base + 1) carries the JSON subtype for arrays and objects -/
  jsonEach : Bool := false
  deriving Inhabited

def SrcInfo.slots (s : SrcInfo) : Nat := if s.width > 0 then s.width else s.cols.size + (if s.rowid.isSome then 1 else 0)

structure Scope where
  srcs : Array SrcInfo := #[]
  deriving Inhabited

structure CteInfo where
  name : String
  id : Nat
  cols : Array String
  affs : Array Aff
  /-- a recursive WITH table inside its own recursive SELECT: the queue's current row -/
  queue : Bool := false

structure CEnv where
  schema : Schema
  scopes : List Scope := []
  ctes : List CteInfo := []
  /-- result-column aliases a WHERE, GROUP BY, HAVING or ORDER BY may name (sqlite resolves them last) -/
  aliases : List (String × Expr) := []

structure CState where
  aggs : Array CAgg := #[]
  allowAgg : Bool := false
  wins : Array CWin := #[]
  allowWin : Bool := false
  nextCte : Nat := 0
  /-- the deepest outer frame referred to since the last reset -/
  outer : Nat := 0

abbrev CM := StateT CState (Except String)

/-- A compiled expression's affinity and collation (`true`: written with COLLATE). -/
abbrev Typed := CExpr × Aff × Option (Collation × Bool)

def isAggName (n : String) (nargs : Nat) (star : Bool) : Bool :=
  match n with
  | "COUNT" => star || nargs == 1
  | "SUM" | "TOTAL" | "AVG" => nargs == 1
  | "MIN" | "MAX" => nargs == 1
  | "GROUP_CONCAT" | "STRING_AGG" => nargs == 1 || nargs == 2
  | "JSON_GROUP_ARRAY" => nargs == 1
  | "JSON_GROUP_OBJECT" => nargs == 2
  | "MEDIAN" => nargs == 1
  | "PERCENTILE" | "PERCENTILE_CONT" | "PERCENTILE_DISC" => nargs == 2
  | _ => false

/-- The scalar functions and their argument counts (none: any number from the given minimum). -/
def scalarArity (n : String) : Option (Nat × Option Nat) :=
  -- the JSON functions check their own arguments
  if Json.isJsonFn n then some (0, none) else
  match n with
  | "ABS" | "LENGTH" | "LOWER" | "UPPER" | "TYPEOF" | "HEX" | "QUOTE" | "UNICODE" | "OCTET_LENGTH" | "LIKELY"
  | "UNLIKELY" | "SIGN" | "SQRT" | "EXP" | "LN" | "LOG10" | "LOG2" | "CEIL" | "CEILING" | "FLOOR" | "TRUNC" | "SIN"
  | "COS" | "TAN" | "ASIN" | "ACOS" | "ATAN" | "SINH" | "COSH" | "TANH" | "ASINH" | "ACOSH" | "ATANH" | "DEGREES"
  | "RADIANS" | "ZEROBLOB" | "UNHEX" | "SOUNDEX" | "RANDOMBLOB" => some (1, some 1)
  | "IFNULL" | "NULLIF" | "INSTR" | "POW" | "POWER" | "ATAN2" | "MOD" | "LIKELIHOOD" | "GLOB" => some (2, some 2)
  | "LIKE" => some (2, some 3)
  | "SUBSTR" | "SUBSTRING" => some (2, some 3)
  | "REPLACE" => some (3, some 3)
  | "IIF" | "IF" => some (2, some 3)
  | "TRIM" | "LTRIM" | "RTRIM" | "ROUND" | "LOG" => some (1, some 2)
  | "COALESCE" => some (2, none)
  | "MIN" | "MAX" => some (2, none)
  | "CHAR" | "CONCAT" => some (0, none)
  | "CONCAT_WS" => some (1, none)
  | "PRINTF" | "FORMAT" => some (0, none)
  | "DATE" | "TIME" | "DATETIME" | "JULIANDAY" | "UNIXEPOCH" => some (0, none)
  | "STRFTIME" => some (1, none)
  | "TIMEDIFF" => some (2, some 2)
  | "CURRENT_DATE" | "CURRENT_TIME" | "CURRENT_TIMESTAMP" => some (0, some 0)
  | "PI" | "LAST_INSERT_ROWID" | "CHANGES" | "TOTAL_CHANGES" | "SQLITE_VERSION" | "RANDOM" | "SQLITE_SOURCE_ID" => some (0, some 0)
  | _ => none

/-- sqlite3CompareAffinity: numeric if either side is numeric, else the side that has an affinity's (none and blob convert
nothing). -/
def cmpAff (a b : Aff) : Aff :=
  match a, b with
  | .none, x | x, .none => x
  | x, y => if x.isNumeric || y.isNumeric then .numeric else .blob

/-- The comparison's collation: the leftmost COLLATE, else the left column's, else the right column's, else BINARY. -/
def cmpColl (a b : Option (Collation × Bool)) : Collation :=
  match a, b with
  | some (c, true), _ => c
  | _, some (c, true) => c
  | some (c, _), _ => c
  | _, some (c, _) => c
  | none, none => .binary

/-- Only an explicit COLLATE passes through an operator. -/
def explicitOnly (a b : Option (Collation × Bool)) : Option (Collation × Bool) :=
  match a, b with
  | some (c, true), _ => some (c, true)
  | _, some (c, true) => some (c, true)
  | _, _ => none

/-- Splits an AND tree into its conjuncts. -/
def conjuncts : Expr → Nat → List Expr
  | .bin .and a b, fuel+1 => conjuncts a fuel ++ conjuncts b fuel
  | e, _ => [e]

def ordinalName (n : Nat) : String :=
  match n with
  | 1 => "1st" | 2 => "2nd" | 3 => "3rd" | n => s!"{n}th"

/-- Column `(tbl.)name` in one scope: its slot, affinity and collation. -/
def resolveIn (sc : Scope) (tbl : Option String) (name : String) : Except String (Option (Nat × Aff × Collation)) := do
  let mut found : Option (Nat × Aff × Collation) := none
  let mut count := 0
  for s in sc.srcs do
    if let some t := tbl then
      unless nameEq s.name t do continue
    match s.cols.findIdx? (nameEq · name) with
    | some i =>
      if tbl.isNone && s.hidden.getD i false then continue
      if found.isNone then found := some (s.base + i, s.affs.getD i .none, s.colls.getD i .binary)
      count := count + 1
    | none =>
      if (nameEq name "rowid" || nameEq name "oid" || nameEq name "_rowid_") then
        if let some r := s.rowid then
          if found.isNone then found := some (r, .integer, .binary)
          count := count + 1
  if count > 1 && tbl.isNone then throw s!"ambiguous column name: {name}"
  return found

def resolve (scopes : List Scope) (tbl : Option String) (name : String) (depth : Nat := 0) :
    Except String (Option (Nat × Nat × Aff × Collation)) :=
  match scopes with
  | [] => .ok none
  | sc :: rest => do
    match ← resolveIn sc tbl name with
    | some (s, a, c) => return some (depth, s, a, c)
    | none => resolve rest tbl name (depth + 1)

/-- The depth-0 slots an expression reads, and whether it holds a correlated subquery. -/
def slotsOf : CExpr → Nat → Array Nat × Bool
  | _, 0 => (#[], true)
  | e, fuel+1 =>
    let go (es : Array CExpr) : Array Nat × Bool :=
      es.foldl (fun (acc, c) x => let (s, c2) := slotsOf x fuel; (acc ++ s, c || c2)) (#[], false)
    match e with
    | .lit _ | .agg _ => (#[], false)
    | .col 0 s => (#[s], false)
    | .col _ _ => (#[], false)
    | .arith _ a b | .cmp _ a b _ _ | .and a b | .or a b => go #[a, b]
    | .not a | .neg a | .bitNot a | .cast a _ | .isNull a _ => slotsOf a fuel
    | .fn _ args => go args
    | .case b ws e _ _ => go (((b.toArray ++ ws.map (·.1)) ++ ws.map (·.2)) ++ e.toArray)
    | .inList e items _ _ _ => go (#[e] ++ items)
    | .inVals e _ _ _ _ _ => slotsOf e fuel
    | .inSel e _ _ _ _ corr => let (s, c) := slotsOf e fuel; (s, c || corr)
    | .exists _ _ corr | .scalar _ corr => (#[], corr)
    | .matchE _ e p esc _ => go (#[e, p] ++ esc.toArray)
    | .inSelRow es _ _ _ _ => let (s, _) := go es; (s, true)
    | .win _ => (#[], false)
    | .raise _ _ => (#[], false)

/-- The FROM item that owns a slot. -/
def srcOfSlot (bases : Array Nat) (slot : Nat) : Nat :=
  (bases.toList.zipIdx.filter (fun (b, _) => b ≤ slot)).getLast?.map (·.2) |>.getD 0

/-- A conjunct as a constraint on slot `s`: `(op, other side, affinity, collation)` with the column on the left. -/
def asConstraint (c : CExpr) : Option (Nat × BinOp × CExpr × Aff × Collation) :=
  let flip : BinOp → BinOp
    | .lt => .gt | .le => .ge | .gt => .lt | .ge => .le | o => o
  match c with
  | .cmp op (.col 0 s) e aff coll => if op == .is || op == .isNot || op == .ne then none else some (s, op, e, aff, coll)
  | .cmp op e (.col 0 s) aff coll => if op == .is || op == .isNot || op == .ne then none else some (s, flip op, e, aff, coll)
  | _ => none

/-- Chooses how to find a table's rows from the conjuncts that constrain it. `bound`: an expression is usable when it
reads only slots below the table's. -/
def chooseAccess (t : Table) (idxs : Array Index) (base : Nat) (conds : Array CExpr) : Access CExpr :=
  let rowidSlot := base + t.cols.size
  let isRowid (s : Nat) : Bool := s == rowidSlot || (t.ipk.map (base + ·) == some s)
  let usable (e : CExpr) : Bool := let (ss, corr) := slotsOf e 64; !corr && ss.all (· < base)
  let cons := conds.filterMap fun c => match asConstraint c with
    | some (s, op, e, aff, coll) => if s ≥ base && s ≤ rowidSlot && usable e then some (s, op, e, aff, coll) else none
    | none => none
  -- an equality between two columns, this table's on the right
  let cons := cons ++ conds.filterMap fun c => match c with
    | .cmp .eq e (.col 0 s) aff coll => if s ≥ base && s ≤ rowidSlot && usable e then some (s, .eq, e, aff, coll) else none
    | _ => none
  -- rowid = e
  match cons.find? (fun (s, op, _, _, _) => isRowid s && op == .eq) with
  | some (_, _, e, _, _) => .rowidEq e
  | none =>
  -- rowid IN (list)
  let inl := conds.findSome? fun c => match c with
    | .inList (.col 0 s) items false _ _ => if isRowid s && items.all usable then some items else none
    | _ => none
  match inl with
  | some items => .rowidIn items
  | none =>
  -- an index: the longest equality prefix, then a range on the next column
  let idxPlans := idxs.filterMap fun ix =>
    if ix.pred.isSome || ix.hasExprs then none else
    let eqs := (List.range ix.cols.size).foldl (fun (acc : Array (CExpr × Aff) × Bool) k =>
      if !acc.2 then acc else
      let c := ix.cols.getD k 0
      match cons.find? (fun (s, op, _, _, coll) => s == base + c && op == .eq && coll == ix.colls.getD k .binary) with
      | some (_, _, e, aff, _) => (acc.1.push (e, aff), true)
      | none => (acc.1, false)) (#[], true) |>.1
    let k := eqs.size
    let rangeOk := k < ix.cols.size && !(ix.desc.getD k false)
    let c := ix.cols.getD k 0
    let rng (ops : List BinOp) : Option (CExpr × Bool × Aff) :=
      if !rangeOk then none else
      cons.findSome? fun (s, op, e, aff, coll) =>
        if s == base + c && ops.contains op && coll == ix.colls.getD k .binary then some (e, op == .ge || op == .le, aff)
        else none
    let lo := rng [.gt, .ge]
    let hi := rng [.lt, .le]
    if eqs.isEmpty && lo.isNone && hi.isNone then none
    else some (eqs.size * 4 + (if ix.unique && eqs.size == ix.cols.size then 2 else 0) + (if lo.isSome || hi.isSome then 1 else 0),
               Access.index ix.root ix.keyInfo eqs lo hi)
  let best := idxPlans.foldl (fun (b : Option (Nat × Access CExpr)) (sc, a) => match b with
    | some (bs, _) => if sc > bs then some (sc, a) else b
    | none => some (sc, a)) none
  match best with
  | some (sc, a) => if sc ≥ 4 then a else
    match rowidRange cons isRowid with
    | some r => r
    | none => a
  | none => (rowidRange cons isRowid).getD .full
where
  rowidRange (cons : Array (Nat × BinOp × CExpr × Aff × Collation)) (isRowid : Nat → Bool) : Option (Access CExpr) :=
    let lo := cons.findSome? fun (s, op, e, _, _) => if isRowid s && (op == .gt || op == .ge) then some (e, op == .ge) else none
    let hi := cons.findSome? fun (s, op, e, _, _) => if isRowid s && (op == .lt || op == .le) then some (e, op == .le) else none
    if lo.isNone && hi.isNone then none else some (.rowidRange lo hi)

/-- The keys of a transient index for an inner FROM item read whole (sqlite's automatic index): the equalities between
one of its `ncols` columns from slot `base` (not `rowid`, a rowid alias) and an expression over the earlier items,
one per column. -/
def autoKeys (base ncols : Nat) (rowid : Option Nat) (conds : Array CExpr) : Array (Nat × CExpr × Aff × Collation) :=
  let usable (e : CExpr) : Bool := let (ss, corr) := slotsOf e 64; !corr && ss.all (· < base)
  let key (s : Nat) (e : CExpr) (aff : Aff) (coll : Collation) : Option (Nat × CExpr × Aff × Collation) :=
    if s ≥ base && s < base + ncols && rowid != some s && usable e then some (s, e, aff, coll) else none
  conds.foldl (fun ks c =>
    -- the column on either side
    let k := match c with
      | .cmp .eq (.col 0 s) e aff coll => key s e aff coll
      | _ => none
    let k := k <|> match c with
      | .cmp .eq e (.col 0 s) aff coll => key s e aff coll
      | _ => none
    match k with
    | some k => if ks.any (·.1 == k.1) then ks else ks.push k
    | none => ks) #[]

/-- CAST to an affinity. -/
def castV (aff : Aff) (v : Value) : Value :=
  match v with
  | .null => .null
  | v => match aff with
    | .integer => .int (Num.castToInt v)
    | .real => .real (Num.castToReal v)
    | .numeric => Num.castToNumeric v
    | .text => .text v.toText
    | .blob | .none => .blob v.toBytes

/-- Unary minus of a constant: text and blobs read as numbers; the smallest Int64 negates to a real. -/
def negConst : Value → Value
  | .null => .null
  | .int i => if i == Int64.minValue then .real (-i.toFloat) else .int (-i)
  | .real f => .real (-f)
  | v => match Num.castToNumeric v with
    | .int i => if i == Int64.minValue then .real (-i.toFloat) else .int (-i)
    | .real f => .real (-f)
    | _ => .int 0

/-- sqlite3ValueFromExpr on a DEFAULT: the value of a literal, unary + or -, or CAST of those; any other expression has none. -/
def constDefault? : Expr → Option Value
  | .lit v => some v
  | .un .pos e => constDefault? e
  | .un .neg e => (constDefault? e).map negConst
  | .cast e t => (constDefault? e).map (castV (Aff.ofType t))
  | _ => none

/-- A column's default as a stored value: a row older than the column (ALTER TABLE ADD COLUMN) reads it through the column's affinity. -/
def columnDefault (c : Column) : Value := Value.applyAff c.aff ((c.default.bind constDefault?).getD .null)

def stripCollate (e : Expr) : Expr := match e with | .collate x _ => x | x => x

/-- An ORDER BY term's direction, NULLs placement and collation (a result column's, unless it has COLLATE). -/
def dirOf (t : OrderTerm) (names : Array String) (colls : Array (Option (Collation × Bool))) : Bool × Bool × Collation :=
  match t with
  | .mk e desc nf =>
    let coll := match e with
      | .collate _ c => (Collation.ofName? c).getD .binary
      | e => match e with
        | .lit (.int k) => ((colls.getD (k.toNatClampNeg - 1) none).map (·.1)).getD .binary
        | .col _ n _ => match names.findIdx? (nameEq · n) with
          | some k => ((colls.getD k none).map (·.1)).getD .binary
          | none => .binary
        | _ => .binary
    (desc, nf.getD (!desc), coll)

def opName : CompoundOp → String
  | .union => "UNION" | .unionAll => "UNION ALL" | .intersect => "INTERSECT" | .except => "EXCEPT"
/-- an ORDER BY term of a compound: a column number, a result name, or a result column's expression -/
def orderTermColumn (e : Expr) (names : Array String) : Option Nat :=
  match stripCollate e with
  | .lit (.int k) => if k ≥ 1 && k.toNatClampNeg ≤ names.size then some (k.toNatClampNeg - 1) else none
  | .col _ n _ => names.findIdx? (nameEq · n)
  | _ => none
def orderTermColl (e : Expr) : Option Collation :=
  match e with
  | .collate _ c => Collation.ofName? c
  | _ => none
/-- a simple SELECT's ORDER BY term that is a plain column: its declared collation -/
def exprColl (env : CEnv) (core : Core) (e : Expr) : Option Collation :=
  match core, e with
  | .select _ _ (some (.table tn _)) [] _ _ _, .col _ n _ =>
    (env.schema.table? tn).bind fun t => t.colIndex? n |>.map fun i => (t.cols.getD i default).coll
  | _, _ => none
/-- a plain column's result name: its declared name -/
def colName (infos : Array SrcInfo) (tbl : Option String) (n : String) : String :=
  let hit := infos.findSome? fun s =>
    if (match tbl with | some t => nameEq s.name t | none => true) then
      (s.cols.find? (nameEq · n)) else none
  hit.getD n
def isOuter : CSource → Bool
  | .table _ _ _ _ _ _ _ l r _ _ | .sub _ _ _ l r _ _ | .cte _ _ _ l r _ _ | .tvf _ _ _ _ l r _ => l || r
def isRightOuter : CSource → Bool
  | .table _ _ _ _ _ _ _ _ r _ _ | .sub _ _ _ _ r _ _ | .cte _ _ _ _ r _ _ | .tvf _ _ _ _ _ r _ => r

/-- An ORDER BY term's direction, NULLs placement and collation, in a window. -/
def winDir (o : OrderTerm) (t : Typed) : Bool × Bool × Collation :=
  match o with
  | .mk e desc nf =>
    (desc, nf.getD (!desc), match e with
      | .collate _ c => (Collation.ofName? c).getD .binary
      | _ => (t.2.2.map fun (k : Collation × Bool) => k.1).getD .binary)

def winNames : List String := ["ROW_NUMBER", "RANK", "DENSE_RANK", "PERCENT_RANK", "CUME_DIST", "NTILE", "LAG", "LEAD",
  "FIRST_VALUE", "LAST_VALUE", "NTH_VALUE", "COUNT", "SUM", "TOTAL", "AVG", "MIN", "MAX", "GROUP_CONCAT", "STRING_AGG",
  "JSON_GROUP_ARRAY", "JSON_GROUP_OBJECT", "MEDIAN", "PERCENTILE", "PERCENTILE_CONT", "PERCENTILE_DISC"]

/-- Row values compared: `=`/`IS` (and `!=`/`IS NOT` negated) pairwise, `< <= > >=` left to right. -/
def rowCmp (op : BinOp) : List Expr → List Expr → Nat → Expr
  | [], [], _ => .lit (.int (if op == .eq || op == .is || op == .le || op == .ge then 1 else 0))
  | _, _, 0 => .lit .null
  | [a], [b], _ => .bin op a b
  | a :: as, b :: bs, f+1 =>
    match op with
    | .eq | .is => .bin .and (.bin op a b) (rowCmp op as bs f)
    | .ne => .un .not (rowCmp .eq (a :: as) (b :: bs) f)
    | .isNot => .un .not (rowCmp .is (a :: as) (b :: bs) f)
    | .lt | .gt => .bin .or (.bin op a b) (.bin .and (.bin .eq a b) (rowCmp op as bs f))
    | .le => .bin .or (.bin .lt a b) (.bin .and (.bin .eq a b) (rowCmp op as bs f))
    | .ge => .bin .or (.bin .gt a b) (.bin .and (.bin .eq a b) (rowCmp op as bs f))
    | _ => .lit .null
  | _, _, _ => .lit .null
def tableOfRoot (s : Schema) (root : Pgno) : Option Table := s.tables.find? (·.root == root)
/-- A simple SELECT's first FROM item read through an access path that already gives the ORDER BY keys (sqlite's where.c:
the loop's order satisfies the ORDER BY, so no sorter is used): the item with its path read in that order. The keys are
the rowid, or the columns of the index in use after its equality prefix (then the rowid), each with the index's
collation and the default NULL placement, all in one direction or all in the opposite one (the index read backwards). Keys
after the rowid matter only when the item is not `alone` in the FROM clause (its row then comes with several joined rows). -/
def orderedItem (schema : Schema) (alone : Bool) (src : CSource) (order : Array CExpr) (dirs : Array (Bool × Bool × Collation)) :
    Option CSource :=
  match src with
  | .table root n ipk rc dv base access false false layout on =>
    let isRowid (s : Nat) : Bool := s == base + n || ipk.map (base + ·) == some s
    let withAccess (a : Access CExpr) : Option CSource := some (.table root n ipk rc dv base a false false layout on)
    match order.mapM (fun o => match o with | .col 0 s => some s | _ => none), dirs[0]? with
    | some ss, some (desc0, _, _) =>
      if !layout.isEmpty then none else
      match access with
      -- (one row of the item: keys of its own columns are the same on every output row)
      | .rowidEq _ => if ss.all (fun s => base ≤ s && s ≤ base + n) then withAccess access else none
      | .rowidIn _ => if isRowid (ss.getD 0 0) && !desc0 && (alone || ss.size == 1) then withAccess access else none
      | .full | .rowidRange .. =>
        if isRowid (ss.getD 0 0) && (alone || ss.size == 1) then withAccess (.ordered desc0 access) else none
      | .index iroot _ eqs _ _ => do
        let ix ← (tableOfRoot schema root).bind fun t => (schema.indexesOfTable t).find? (·.root == iroot)
        -- whether key `j` reads backwards, and whether it is the rowid
        let keyBack (j : Nat) : Option (Bool × Bool) := do
          let (d, nf, coll) ← dirs[j]?
          let s ← ss[j]?
          let c := eqs.size + j
          if c < ix.cols.size then
            if s == base + ix.cols.getD c 0 && coll == ix.colls.getD c .binary && nf == !d then some (d != ix.desc.getD c false, false)
            else none
          else if c == ix.cols.size && isRowid s then some (d, true) else none
        let r ← (List.range ss.size).foldl (fun (st : Option (Option Bool × Bool)) j => match st with
          | some (back, false) => do
            let (b, isRowidKey) ← keyBack j
            if back.all (· == b) then some (some b, isRowidKey) else none
          -- (the rowid is unique: no later key matters, unless joined rows follow it)
          | some (back, true) => if alone then some (back, true) else none
          | none => none) (some (none, false))
        withAccess (.ordered (r.1.getD false) access)
      | _ => none
    | _, _ => none
  | _ => none

/-- whether a query reads table `name` (a recursive WITH table refers to itself) -/
def selectReads (q : Select) (name : String) : Bool :=
  match q with
  | .mk _ _ first rest _ _ _ => (first :: rest.map (·.2)).any fun c => match c with
    | .select _ _ (some (.table t _)) js _ _ _ => nameEq t name || js.any fun (.mk _ it _ _) => match it with
      | .table t _ => nameEq t name
      | _ => false
    | .select _ _ _ js _ _ _ => js.any fun (.mk _ it _ _) => match it with
      | .table t _ => nameEq t name
      | _ => false
    | _ => false

mutual
def compileExpr (env : CEnv) : Expr → Nat → CM Typed
  | _, 0 => throw "expression nested too deeply"
  | e, fuel+1 => match e with
  | .lit v => return (.lit v, .none, none)
  | .col tbl name _ => do
    match ← liftM (resolve env.scopes tbl name) with
    | some (d, s, a, c) =>
      modify fun st => { st with outer := max st.outer d }
      let isJsonValue := ((env.scopes.drop d).head?.map fun sc => sc.srcs.any fun si => si.jsonEach && si.base + 1 == s).getD false
      if isJsonValue then return (.fn jsonValueTag #[.col d s, .col d (s + 1)], a, some (c, false))
      return (.col d s, a, some (c, false))
    | none =>
      match tbl, env.aliases.find? (nameEq ·.1 name) with
      | none, some (_, e) => compileExpr { env with aliases := [] } e fuel
      | _, _ => throw (match tbl with | some t => s!"no such column: {t}.{name}" | none => s!"no such column: {name}")
  | .bin op (.row as) (.row bs) => do
    if as.length != bs.length then throw "row value misused"
    if !([BinOp.eq, .ne, .lt, .le, .gt, .ge, .is, .isNot].contains op) then throw "row value misused"
    compileExpr env (rowCmp op as bs (as.length + 1)) fuel
  | .bin _ (.row _) _ | .bin _ _ (.row _) => throw "row value misused"
  | .row _ => throw "row value misused"
  | .between (.row es) (.row lo) (.row hi) neg => do
    if es.length != lo.length || es.length != hi.length then throw "row value misused"
    let r := Expr.bin .and (rowCmp .ge es lo (es.length + 1)) (rowCmp .le es hi (es.length + 1))
    compileExpr env (if neg then .un .not r else r) fuel
  | .inList (.row es) items neg => do
    let eqs ← items.mapM fun it => match it with
      | .row xs => if xs.length == es.length then pure (rowCmp .eq es xs (es.length + 1)) else throw "row value misused"
      | _ => throw "row value misused"
    let any := eqs.foldr (fun e acc => Expr.bin .or e acc) (.lit (.int 0))
    compileExpr env (if neg then .un .not any else any) fuel
  | .inSelect (.row es) q neg => do
    let ces ← compileList env es fuel
    let (cq, _, affs, colls, _) ← compileSub env q fuel
    if cq.ncols != ces.size then throw s!"sub-select returns {cq.ncols} columns - expected {ces.size}"
    let aff := ces.mapIdx fun i (t : Typed) => cmpAff t.2.1 (affs.getD i .none)
    let coll := ces.mapIdx fun i (t : Typed) => cmpColl t.2.2 (colls.getD i none)
    return (.inSelRow (ces.map fun (t : Typed) => t.1) cq neg aff coll, .none, none)
  | .raise k m => return (.raise k m, .none, none)
  | .window name distinct star args filter (.mk partition orderBy frame) => do
    let n := upperAscii name
    let st ← get
    unless st.allowWin do throw s!"misuse of window function {name}()"
    unless winNames.contains n do throw s!"{name}() may not be used as a window function"
    -- the arguments are ordinary expressions (aggregates allowed in an aggregate query), not windows
    set { st with allowWin := false }
    let cargs ← compileList env args fuel
    let cfilter ← match filter with
      | some f => do let r ← compileExpr env f fuel; pure (some r.1)
      | none => pure none
    let cpart ← compileList env partition fuel
    let cord ← compileList env (orderBy.map fun (.mk e _ _) => e) fuel
    let dirs := (orderBy.toArray.zip cord).map fun (p : OrderTerm × Typed) => winDir p.1 p.2
    let bound (b : FrameBound) : CM CBound := match b with
      | .unboundedPreceding => pure .unboundedPreceding
      | .currentRow => pure .currentRow
      | .unboundedFollowing => pure .unboundedFollowing
      | .preceding e => do let r ← compileExpr env e fuel; pure (.preceding r.1)
      | .following e => do let r ← compileExpr env e fuel; pure (.following r.1)
    let (units, s, f, ex) ← match frame with
      | some (.mk u s f ex) => do pure (u, ← bound s, ← bound f, ex)
      | none => pure (if orderBy.isEmpty then (FrameUnits.rows, CBound.unboundedPreceding, CBound.unboundedFollowing, FrameExclude.noOthers)
                      else (.range, .unboundedPreceding, .currentRow, .noOthers))
    modify fun st' => { st' with allowWin := true }
    let st ← get
    set { st with wins := st.wins.push (.mk n distinct star (cargs.map fun (t : Typed) => t.1) cfilter
      (cpart.map fun (t : Typed) => t.1) (cpart.map fun (t : Typed) => (t.2.2.map fun (k : Collation × Bool) => k.1).getD .binary)
      (cord.map fun (t : Typed) => t.1) dirs units s f ex) }
    return (.win st.wins.size, .none, none)
  | .bin op a b => do
    let (ca, aa, ka) ← compileExpr env a fuel
    let (cb, ab, kb) ← compileExpr env b fuel
    match op with
    | .and => return (.and ca cb, .none, none)
    | .or => return (.or ca cb, .none, none)
    | .eq | .ne | .lt | .le | .gt | .ge | .is | .isNot => return (.cmp op ca cb (cmpAff aa ab) (cmpColl ka kb), .none, none)
    | _ => return (.arith op ca cb, .none, explicitOnly ka kb)
  | .un op a => do
    let (ca, _, ka) ← compileExpr env a fuel
    match op with
    | .neg => return (.neg ca, .none, explicitOnly ka none)
    | .pos => return (ca, .none, ka)
    | .not => return (.not ca, .none, none)
    | .bitNot => return (.bitNot ca, .none, none)
  | .fn name distinct star args0 => do
    let n := upperAscii name
    -- an aggregate's FILTER clause rides as the last argument
    let (args, flt) := match args0.getLast? with
      | some (.fn t _ _ [f]) => if t == filterTag then (args0.dropLast, some f) else (args0, none)
      | _ => (args0, none)
    if isAggName n args.length star && (n != "MIN" && n != "MAX" || args.length == 1) then
      let st ← get
      unless st.allowAgg do throw s!"misuse of aggregate function {name}()"
      set { st with allowAgg := false }
      let cargs ← compileList env args fuel
      let cflt ← match flt with
        | some f => do let (c, _, _) ← compileExpr env f fuel; pure (some c)
        | none => pure none
      modify fun st' => { st' with allowAgg := true }
      let st ← get
      let coll := ((cargs[0]?).bind (·.2.2) |>.map (·.1)).getD .binary
      set { st with aggs := st.aggs.push (.mk n distinct star (cargs.map fun (t : Typed) => t.1) coll cflt) }
      return (.agg st.aggs.size, .none, none)
    else if flt.isSome then throw s!"FILTER may not be used with non-aggregate {name}()"
    else
      match scalarArity n with
      | none => throw s!"no such function: {name}"
      | some (lo, hi) =>
        if args.length < lo || (match hi with | some h => args.length > h | none => false) || star then
          throw s!"wrong number of arguments to function {name}()"
        if distinct then throw s!"DISTINCT aggregates must have exactly one argument"
        let cargs ← compileList env args fuel
        -- random() and randomblob(): the call site, so two calls in one row differ
        let cargs ← if n == "RANDOM" || n == "RANDOMBLOB" then do
            let st ← get
            set { st with nextCte := st.nextCte + 1 }
            pure (cargs.push (.lit (.int (st.nextCte.toInt64 * 7919 + 1)), .none, none))
          else pure cargs
        let coll := cargs.foldl (fun (acc : Option (Collation × Bool)) (t : Typed) => match acc with | some _ => acc | none => explicitOnly t.2.2 none) none
        return (.fn n (cargs.map (·.1)), .none, coll)
  | .cast e t => do
    let (ce, _, k) ← compileExpr env e fuel
    let a := Aff.ofType t
    return (.cast ce a, a, k)
  | .collate e c => do
    let (ce, a, _) ← compileExpr env e fuel
    match Collation.ofName? c with
    | some coll => return (ce, a, some (coll, true))
    | none => throw s!"no such collation sequence: {c}"
  | .case (some b) whens els =>
    -- CASE b WHEN w ...: each WHEN compares b = w (with w's collation when it has one)
    compileExpr env (.case none (whens.map fun (w, t) => (.bin .eq b w, t)) els) fuel
  | .case base whens els => do
    let cb ← match base with
      | some b => do let r ← compileExpr env b fuel; pure (some r)
      | none => pure none
    let cw ← compilePairs env whens fuel
    let ce ← match els with
      | some x => do let r ← compileExpr env x fuel; pure (some r.1)
      | none => pure none
    let (aff, coll) := match cb with
      | some (_, a, k) => (cmpAff a .none, cmpColl k none)
      | none => (.none, .binary)
    return (.case (cb.map (·.1)) cw ce aff coll, .none, none)
  | .between e lo hi neg => do
    let (ce, ae, ke) ← compileExpr env e fuel
    let (cl, al, kl) ← compileExpr env lo fuel
    let (ch, ah, kh) ← compileExpr env hi fuel
    let r := CExpr.and (.cmp .ge ce cl (cmpAff ae al) (cmpColl ke kl)) (.cmp .le ce ch (cmpAff ae ah) (cmpColl ke kh))
    return (if neg then .not r else r, .none, none)
  | .inList e items neg => do
    let (ce, ae, ke) ← compileExpr env e fuel
    let ci ← compileList env items fuel
    let aff := ci.foldl (fun (a : Aff) (t : Typed) => if a == ae then cmpAff ae t.2.1 else a) ae
    let aff := if ae == .none then .none else aff
    return (.inList ce (ci.map fun (t : Typed) => t.1) neg aff (cmpColl ke none), .none, none)
  | .inSelect e q neg => do
    let (ce, ae, ke) ← compileExpr env e fuel
    let (cq, _, affs, _, corr) ← compileSub env q fuel
    if cq.ncols != 1 then throw s!"sub-select returns {cq.ncols} columns - expected 1"
    return (.inSel ce cq neg (cmpAff ae (affs.getD 0 .none)) (cmpColl ke none) corr, .none, none)
  | .matches op e p esc neg => do
    let (ce, _, _) ← compileExpr env e fuel
    let (cp, _, _) ← compileExpr env p fuel
    let cesc ← match esc with
      | some x => do let r ← compileExpr env x fuel; pure (some r.1)
      | none => pure none
    if op == .regexp || op == .match then throw s!"no such function: {if op == .regexp then "REGEXP" else "MATCH"}"
    return (.matchE op ce cp cesc neg, .none, none)
  | .isNull e neg => do
    let (ce, _, _) ← compileExpr env e fuel
    return (.isNull ce neg, .none, none)
  | .exists q neg => do
    let (cq, _, _, _, corr) ← compileSub env q fuel
    return (.exists cq neg corr, .none, none)
  | .subquery q => do
    let (cq, _, affs, colls, corr) ← compileSub env q fuel
    return (.scalar cq corr, affs.getD 0 .none, (colls.getD 0 none))
  | .param t => throw s!"lean-sqlite: parameters are not supported: {t}"

def compileList (env : CEnv) : List Expr → Nat → CM (Array Typed)
  | [], _ => return #[]
  | _, 0 => throw "expression nested too deeply"
  | e :: rest, fuel+1 => do
    let c ← compileExpr env e fuel
    let cs ← compileList env rest fuel
    return #[c] ++ cs

def compilePairs (env : CEnv) : List (Expr × Expr) → Nat → CM (Array (CExpr × CExpr))
  | [], _ => return #[]
  | _, 0 => throw "expression nested too deeply"
  | (a, b) :: rest, fuel+1 => do
    let (ca, _, _) ← compileExpr env a fuel
    let (cb, _, _) ← compileExpr env b fuel
    let cs ← compilePairs env rest fuel
    return #[(ca, cb)] ++ cs

/-- A subquery: compiled with its own aggregates, and whether it reads the enclosing rows. -/
def compileSub (env : CEnv) (q : Select) : Nat → CM (CSel × Array String × Array Aff × Array (Option (Collation × Bool)) × Bool)
  | 0 => throw "expression nested too deeply"
  | fuel+1 => do
    let st ← get
    set { st with aggs := #[], allowAgg := false, wins := #[], allowWin := false, outer := 0 }
    let (cq, names, affs, colls) ← compileSelect env q fuel
    let st2 ← get
    set { st2 with aggs := st.aggs, allowAgg := st.allowAgg, wins := st.wins, allowWin := st.allowWin,
                   outer := max st.outer (st2.outer - 1) }
    return (cq, names, affs, colls, st2.outer ≥ 1)

/-- A SELECT: its WITH tables, cores, ORDER BY and LIMIT; also its column names, affinities and collations. -/
def compileSelect (env : CEnv) : Select → Nat → CM (CSel × Array String × Array Aff × Array (Option (Collation × Bool)))
  | _, 0 => throw "query nested too deeply"
  | .mk recursive ctes first rest orderBy limit offset, fuel+1 => do
    -- WITH tables, each visible to the later ones (and a recursive one to itself)
    let (env, cctes) ← compileCtes env recursive ctes fuel
    let single := rest.isEmpty
    let (c0, names, affs, colls) ← compileCore env first (if single then some orderBy else none) fuel
    let mut cores := #[c0]
    let mut ops := #[]
    for (op, core) in rest do
      let (c, ns, _, _) ← compileCore env core none fuel
      if ns.size != names.size then
        throw s!"SELECTs to the left and right of {opName op} do not have the same number of result columns"
      cores := cores.push c
      ops := ops.push op
    -- a compound's ORDER BY names result columns
    if !single && !orderBy.isEmpty then
      let mut ks : Array Nat := #[]
      let mut i := 0
      for .mk e _ _ in orderBy do
        i := i + 1
        let k ← match orderTermColumn e names with
          | some k => pure k
          | none => throw s!"{ordinalName i} ORDER BY term does not match any column in the result set"
        ks := ks.push k
      cores := cores.map fun c => match c with
        | .select srcs pre f g gc h cols rc _ aggs isAgg d w ws => .select srcs pre f g gc h cols rc (ks.map (cols.getD · default)) aggs isAgg d w ws
        | .values rows _ => .values rows ks
    let dirs := orderBy.toArray.map fun (t : OrderTerm) => dirOf t names colls
    -- a plain column's collation for ORDER BY in a simple select
    let dirs := if single then dirs.mapIdx fun i d =>
        let (desc, nf, coll) := d
        match orderBy[i]? with
        | some (.mk e _ _) => if (orderTermColl e).isSome then d else
          match exprColl env first e with
          | some c => (desc, nf, c)
          | none => (desc, nf, coll)
        | none => d
      else dirs
    -- a simple SELECT whose first FROM item's access path gives the ORDER BY needs no sort
    let (cores', dirs) := match cores[0]?, single with
      | some (.select srcs pre f g gc h cols rc order aggs false false w #[]), true =>
        if g.isEmpty && !srcs.any isRightOuter then
          match srcs[0]?.bind fun s => orderedItem env.schema (srcs.size == 1) s order dirs with
          | some s0 => (#[CCore.select (srcs.setIfInBounds 0 s0) pre f g gc h cols rc #[] aggs false false w #[]], #[])
          | none => (cores, dirs)
        else (cores, dirs)
      | _, _ => (cores, dirs)
    cores := cores'
    let cl ← match limit with
      | some e => do let r ← compileExpr { env with scopes := env.scopes } e fuel; pure (some r.1)
      | none => pure none
    let co ← match offset with
      | some e => do let r ← compileExpr env e fuel; pure (some r.1)
      | none => pure none
    return (.mk cctes cores ops dirs cl co names.size, names, affs, colls)

def compileCtes (env : CEnv) (recursive : Bool) : List Cte → Nat → CM (CEnv × Array CCte)
  | [], _ => return (env, #[])
  | _, 0 => throw "query nested too deeply"
  | .mk name cols q :: rest, fuel+1 => do
    let st ← get
    let id := st.nextCte
    set { st with nextCte := id + 1 }
    let selfRef := recursive && selectReads q name
    let (cq, info) ← if selfRef then do
        -- the initial SELECT gives the column names; then the whole query is compiled with the table visible
        let .mk r c first rest2 _ _ _ := q
        let (_, ns, affs, _) ← compileSelect env (.mk r c first [] [] none none) fuel
        let ns := if cols.isEmpty then ns else cols.toArray
        let info : CteInfo := { name, id, cols := ns, affs := affs.map fun _ => .none }
        let env2 := { env with ctes := { info with queue := true } :: env.ctes }
        if rest2.length != 1 then throw s!"lean-sqlite: recursive table {name} must be one SELECT UNION [ALL] one SELECT"
        let (cq, _, _, _) ← compileSelect env2 q fuel
        pure (cq, info)
      else do
        let (cq, ns, affs, _) ← compileSelect env q fuel
        if !cols.isEmpty && cols.length != ns.size then
          throw s!"table {name} has {ns.size} values for {cols.length} columns"
        let ns := if cols.isEmpty then ns else cols.toArray
        pure (cq, { name, id, cols := ns, affs : CteInfo })
    let env := { env with ctes := info :: env.ctes }
    let (env, more) ← compileCtes env recursive rest fuel
    return (env, #[.mk id cq selfRef] ++ more)

/-- One core: FROM, WHERE, GROUP BY, HAVING and the result columns (and, for a simple SELECT, ORDER BY). -/
def compileCore (env : CEnv) (core : Core) (orderBy : Option (List OrderTerm)) :
    Nat → CM (CCore × Array String × Array Aff × Array (Option (Collation × Bool)))
  | 0 => throw "query nested too deeply"
  | fuel+1 => match core with
  | .values rows => do
    let mut crows := #[]
    let mut affs := #[]
    for r in rows do
      let cr ← compileList env r fuel
      if !crows.isEmpty && cr.size != (crows.getD 0 #[]).size then throw "all VALUES must have the same number of terms"
      crows := crows.push (cr.map fun (t : Typed) => t.1)
      if affs.isEmpty then affs := cr.map fun _ => Aff.none
    let n := (crows.getD 0 #[]).size
    let names := (List.range n).toArray.map fun i => s!"column{i+1}"
    let order ← match orderBy with
      | some terms => terms.toArray.mapM fun (.mk e _ _) => match orderTermColumn e names with
        | some k => pure k
        | none => throw "1st ORDER BY term does not match any column in the result set"
      | none => pure #[]
    return (.values crows order, names, affs, names.map fun _ => none)
  | .select distinct cols fromItem joins whereE groupBy having => do
    -- the FROM items and their slots
    let items := (match fromItem with | some f => [(JoinKind.inner, f, (none : Option Expr), ([] : List String))] | none => [])
      ++ joins.map fun (.mk k it on u) => (k, it, on, u)
    let (srcs, infos, onConds, _) ← compileFrom env items fuel
    let scope : Scope := { srcs := infos }
    let env' := { env with scopes := scope :: env.scopes }
    let width := infos.foldl (fun w s => max w (s.base + s.slots)) 0
    -- result columns
    let st ← get
    set { st with allowAgg := true, aggs := #[], allowWin := true, wins := #[] }
    let mut ccols : Array CExpr := #[]
    let mut names : Array String := #[]
    let mut affs : Array Aff := #[]
    let mut colls : Array (Option (Collation × Bool)) := #[]
    for rc in cols do
      match rc with
      | .star =>
        if infos.isEmpty then throw "no tables specified"
        for s in infos do
          for i in [0:s.cols.size] do
            unless s.hidden.getD i false do
              ccols := ccols.push (.col 0 (s.base + i)); names := names.push (s.cols.getD i "")
              affs := affs.push (s.affs.getD i .none); colls := colls.push (some (s.colls.getD i .binary, false))
      | .tableStar t =>
        match infos.find? (nameEq ·.name t) with
        | none => throw s!"no such table: {t}"
        | some s =>
          for i in [0:s.cols.size] do
            ccols := ccols.push (.col 0 (s.base + i)); names := names.push (s.cols.getD i "")
            affs := affs.push (s.affs.getD i .none); colls := colls.push (some (s.colls.getD i .binary, false))
      | .expr e alias span =>
        let (ce, a, k) ← compileExpr env' e fuel
        ccols := ccols.push ce; affs := affs.push a; colls := colls.push k
        names := names.push (match alias with
          | some n => n
          | none => match e with
            | .col tbl n _ => colName infos tbl n
            | _ => span)
    -- WHERE (no aggregates, no windows), ON
    modify fun st => { st with allowAgg := false, allowWin := false }
    let aliasList := cols.filterMap fun | .expr e (some a) _ => some (a, e) | _ => none
    let env' := { env' with aliases := aliasList }
    let whereConds ← compileList env' (match whereE with | some w => conjuncts w 64 | none => []) fuel
    -- GROUP BY: a number or an alias names a result column
    let mut cgroup : Array CExpr := #[]
    let mut gcolls : Array Collation := #[]
    for g in groupBy do
      match g with
      | .lit (.int k) =>
        if k < 1 || k.toNatClampNeg > ccols.size then throw s!"{ordinalName cgroup.size.succ} GROUP BY term out of range - should be between 1 and {ccols.size}"
        cgroup := cgroup.push (ccols.getD (k.toNatClampNeg - 1) default)
        gcolls := gcolls.push (((colls.getD (k.toNatClampNeg - 1) none).map (·.1)).getD .binary)
      | _ =>
        let (c, _, k) ← compileExpr env' g fuel
        cgroup := cgroup.push c
        gcolls := gcolls.push ((k.map (·.1)).getD .binary)
    modify fun st => { st with allowAgg := true }
    let chaving ← match having with
      | some h => do let r ← compileExpr env' h fuel; pure (some r.1)
      | none => pure none
    -- ORDER BY of a simple SELECT: a number or an alias names a result column, else an expression over the FROM items
    modify fun st => { st with allowWin := true }
    let corder ← match orderBy with
      | none => pure #[]
      | some terms => do
        let mut out := #[]
        let mut i := 0
        for .mk e _ _ in terms do
          i := i + 1
          let e0 := stripCollate e
          match e0 with
          | .lit (.int k) =>
            if k < 1 || k.toNatClampNeg > ccols.size then
              throw s!"{ordinalName i} ORDER BY term out of range - should be between 1 and {ccols.size}"
            out := out.push (ccols.getD (k.toNatClampNeg - 1) default)
          | .col none n _ =>
            match cols.findIdx? (fun | .expr _ (some a) _ => nameEq a n | _ => false) with
            | some j => out := out.push (ccols.getD j default)
            | none => let (c, _, _) ← compileExpr env' e0 fuel; out := out.push c
          | _ => let (c, _, _) ← compileExpr env' e0 fuel; out := out.push c
        pure out
    let st ← get
    let aggs := st.aggs
    let wins := st.wins
    set { st with aggs := #[], allowAgg := false, wins := #[], allowWin := false }
    if !aggs.isEmpty && infos.isEmpty && false then throw ""
    let isAgg := !aggs.isEmpty || !cgroup.isEmpty
    if chaving.isSome && !isAgg then throw "a GROUP BY clause is required before HAVING"
    -- where each condition is checked, and how each table is read
    let bases := infos.map (·.base)
    if (srcs.filter isRightOuter).size > 1 then throw "lean-sqlite: only one RIGHT or FULL JOIN per SELECT is supported"
    let allConds := whereConds.map (fun (t : Typed) => t.1) ++ onConds.filterMap fun (j, c) =>
      if isOuter (srcs.getD j default) then none else some c
    let leftOn : Array (Array CExpr) := (List.range srcs.size).toArray.map fun j =>
      (onConds.filter fun (k, _) => k == j).map (·.2) |>.filter fun _ => isOuter (srcs.getD j default)
    let level (c : CExpr) : Option Nat :=
      let (ss, corr) := slotsOf c 64
      if corr then some (srcs.size - 1) else
      ss.foldl (fun (acc : Option Nat) s => let j := srcOfSlot bases s; some (max (acc.getD 0) j)) none
    let pre := allConds.filter fun c => (level c).isNone || srcs.isEmpty
    let filters := (List.range srcs.size).toArray.map fun j =>
      allConds.filter fun c => !srcs.isEmpty && level c == some j
    let srcs : Array CSource := srcs.mapIdx fun j s => match s with
      | .table root n ipk rc dv base _ left right layout _ =>
        let conds := if left || right then leftOn.getD j #[] else allConds
        let tbl := tableOfRoot env.schema root
        -- a RIGHT/FULL item is read whole (its unmatched rows are found after the join); so is a WITHOUT ROWID table
        let acc := match tbl with
          | some t => if right || t.withoutRowid then .full else chooseAccess t (env.schema.indexesOfTable t) base conds
          | none => .full
        .table root n ipk rc dv base acc left right layout (leftOn.getD j #[])
      | .sub q n base left right _ _ => .sub q n base left right (leftOn.getD j #[]) #[]
      | .cte id n base left right _ _ => .cte id n base left right (leftOn.getD j #[]) #[]
      | .tvf tr args n base left right _ => .tvf tr args n base left right (leftOn.getD j #[])
    -- an inner item read whole gets a transient index, unless each earlier item gives one row (a rowid lookup, a
    -- recursive WITH table's queue row)
    let oneRow (s : CSource) : Bool := match s with
      | .table _ _ _ _ _ _ (.rowidEq _) _ _ _ _ => true
      | .cte id .. => env.ctes.any fun c => c.id == id && c.queue
      | _ => false
    let srcs : Array CSource := if srcs.size < 2 then srcs else srcs.mapIdx fun j s =>
      if j == 0 || (srcs.extract 0 j).all oneRow then s else
      let keys (base n : Nat) (rowid : Option Nat) (left : Bool) (on : Array CExpr) :=
        autoKeys base n rowid (if left then on else allConds)
      match s with
      | .table root n ipk rc dv base .full left false layout on =>
        let ks := if layout.isEmpty then keys base n (ipk.map (base + ·)) left on else #[]
        .table root n ipk rc dv base (if ks.isEmpty then .full else .auto ks) left false layout on
      | .sub q n base left false on _ => .sub q n base left false on (keys base n none left on)
      | .cte id n base left false on _ => .cte id n base left false on (keys base n none left on)
      | s => s
    let rcolls := colls.map fun k => (k.map (·.1)).getD .binary
    return (.select srcs pre filters cgroup gcolls chaving ccols rcolls corder aggs isAgg distinct width wins, names, affs, colls)

/-- The FROM items: sources, their scope entries, and the ON conditions (with the item each belongs to). -/
def compileFrom (env : CEnv) : List (JoinKind × FromItem × Option Expr × List String) → Nat →
    CM (Array CSource × Array SrcInfo × Array (Nat × CExpr) × Nat)
  | [], _ => return (#[], #[], #[], 0)
  | _, 0 => throw "query nested too deeply"
  | items, fuel+1 => do
    let mut srcs : Array CSource := #[]
    let mut infos : Array SrcInfo := #[]
    let mut ons : Array (Nat × CExpr) := #[]
    let mut slot := 0
    for (kind, item, on, usingCols) in items do
      let left := kind == .left || kind == .full
      let right := kind == .right || kind == .full
      let j := srcs.size
      let (src, info) ← match item with
        | .table qname alias =>
          let name := (Schema.splitQual qname).2
          let an := alias.getD name
          match env.ctes.find? (nameEq ·.name name) with
          | some c =>
            pure (CSource.cte c.id c.cols.size slot left right #[] #[],
              { name := an, cols := c.cols, affs := c.affs, colls := c.cols.map fun _ => .binary, base := slot,
                rowid := none, hidden := c.cols.map fun _ => false : SrcInfo })
          | none =>
          match env.schema.view? qname with
          | some v =>
            let (cq, ns, affs, colls, _) ← compileSub { env with scopes := [] } v.q fuel
            let ns := if v.cols.isEmpty then ns else v.cols.toArray
            pure (CSource.sub cq ns.size slot left right #[] #[],
              { name := an, cols := ns, affs, colls := colls.map fun c => (c.map (·.1)).getD .binary, base := slot,
                rowid := none, hidden := ns.map fun _ => false : SrcInfo })
          | none =>
          let tbl := if nameEq name "sqlite_schema" || nameEq name "sqlite_master" then some schemaTable
            else if nameEq name "sqlite_temp_schema" || nameEq name "sqlite_temp_master" then
              some { schemaTable with name := "sqlite_temp_schema", root := tempRoot }
            else env.schema.table? qname
          match tbl with
          | none => throw s!"no such table: {name}"
          | some t =>
            let n := t.cols.size
            pure (CSource.table t.root n t.ipk (t.cols.map (·.aff == .real)) (t.cols.map columnDefault) slot .full
                left right t.layout #[],
              { name := an, cols := t.cols.map (·.name), affs := t.cols.map (·.aff), colls := t.cols.map (·.coll),
                base := slot, rowid := if t.withoutRowid then none else some (slot + n), hidden := t.cols.map fun _ => false,
                width := n + 1 : SrcInfo })
        | .call fname args alias =>
          let n := lowerAscii fname
          if n.startsWith "pragma_" then
            -- a schema pragma's rows, read for each row of the earlier items (the argument may name their columns)
            match schemaPragma env.schema (n.drop 7).toString "" with
            | none => throw s!"no such table-valued function: {fname}"
            | some (ns, _) =>
              let env' := { env with scopes := { srcs := infos } :: env.scopes }
              let cargs ← compileList env' args fuel
              pure (CSource.tvf n (cargs.map (·.1)) ns.size slot left right #[],
                { name := alias.getD fname, cols := ns, affs := ns.map fun _ => .none, colls := ns.map fun _ => .binary,
                  base := slot, rowid := none, hidden := ns.map fun _ => false : SrcInfo })
          else if n == "json_each" || n == "json_tree" then
            -- read per row of the earlier items: the arguments may name their columns
            let env' := { env with scopes := { srcs := infos } :: env.scopes }
            let cargs ← compileList env' args fuel
            if cargs.isEmpty || cargs.size > 2 then throw s!"wrong number of arguments to function {fname}()"
            let ns := #["key", "value", "type", "atom", "id", "parent", "fullkey", "path"]
            pure (CSource.tvf n (cargs.map (·.1)) ns.size slot left right #[],
              { name := alias.getD fname, cols := ns, affs := ns.map fun _ => .none, colls := ns.map fun _ => .binary,
                base := slot, rowid := none, hidden := ns.map fun _ => false, jsonEach := true : SrcInfo })
          else throw s!"no such table-valued function: {fname}"
        | .subquery q alias =>
          let (cq, ns, affs, colls, _) ← compileSub { env with scopes := env.scopes } q fuel
          pure (CSource.sub cq ns.size slot left right #[] #[],
            { name := alias.getD "", cols := ns, affs, colls := colls.map fun c => (c.map (·.1)).getD .binary, base := slot,
              rowid := none, hidden := ns.map fun _ => false : SrcInfo })
      let info := info
      -- USING: an equality with the column of an earlier item; the later column is merged away
      let mut info := info
      -- NATURAL: the columns this item shares with the earlier ones
      let usingCols := if usingCols == ["*"] then
          info.cols.toList.filter fun c => infos.any fun s => s.cols.toList.zipIdx.any fun (n, i) => nameEq n c && !(s.hidden.getD i false)
        else usingCols
      for u in usingCols do
        let some ri := info.cols.findIdx? (nameEq · u) | throw s!"cannot join using column {u} - column not present in both tables"
        let some (li, l) := (infos.toList.zipIdx.findSome? fun (s, _) =>
            (s.cols.findIdx? (nameEq · u)).bind fun ci => if s.hidden.getD ci false then none else some (s.base + ci, s))
          | throw s!"cannot join using column {u} - column not present in both tables"
        ons := ons.push (j, .cmp .eq (.col 0 li) (.col 0 (info.base + ri)) (cmpAff (l.affs.getD 0 .none) .none) (l.colls.getD 0 .binary))
        info := { info with hidden := info.hidden.setIfInBounds ri true }
      infos := infos.push info
      srcs := srcs.push src
      slot := slot + info.slots
      -- ON sees this item and the earlier ones
      if let some o := on then
        let env' := { env with scopes := { srcs := infos } :: env.scopes }
        let cs ← compileList env' (conjuncts o 64) fuel
        ons := ons ++ cs.map fun (c, _, _) => (j, c)
    return (srcs, infos, ons, slot)
end

end LSql

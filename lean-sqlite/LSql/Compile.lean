import LSql.Plan
import LSql.Pragma
import LSql.Json
/-! Compiling the AST: name resolution (resolve.c), comparison affinity and collation (expr.c sqlite3CompareAffinity,
sqlite3ExprCollSeq), aggregate collection, and access-path choice per table (where.c, much reduced). Recursion is bounded
by `fuel` (an expression or query nesting depth). -/
namespace LSql

structure CteInfo where
  name : String
  id : Nat
  cols : Array String
  affs : Array Aff
  /-- a recursive WITH table inside its own recursive SELECT: the queue's current row -/
  queue : Bool := false
  /-- its SELECT, when a FROM item naming it may read it in place (not recursive, not MATERIALIZED) -/
  body : Option Select := none
  /-- how many scopes enclose its WITH clause -/
  nscopes : Nat := 0

mutual
/-- A result column of a FROM item read in place: a column of one of its own items (`*`), an expression over its
items, or column `i` of one of its items that is itself read in place. -/
inductive FlatCol where
  | slot (s : Nat)
  | expr (e : Expr)
  | ref (si : SrcInfo) (i : Nat)

structure SrcInfo where
  name : String
  cols : Array String
  affs : Array Aff
  colls : Array Collation
  base : Nat
  rowid : Option Nat
  /-- columns USING merged into an earlier source's: not seen by `*` or by unqualified names (one past its end: not hidden) -/
  hidden : Array Bool := #[]
  /-- the slots it takes (0: its columns, and its rowid's when it has one) -/
  width : Nat := 0
  /-- json_each / json_tree: its `value` column (slot base + 1) carries the JSON subtype for arrays and objects -/
  jsonEach : Bool := false
  /-- a subquery read in place (select.c flattenSubquery): column `i` is `flat[i]` over `inner`, the subquery's own
  FROM items (their slots in this frame), compiled with the WITH tables `flatCtes` and `flatPad` empty scopes in front
  of the enclosing ones; `flatNull`: the rowid slot that is NULL on a LEFT JOIN's missing row. It takes no slots. -/
  flat : Array FlatCol := #[]
  inner : Array SrcInfo := #[]
  flatCtes : List CteInfo := []
  flatPad : Nat := 0
  flatNull : Option Nat := none
end

instance : Inhabited SrcInfo := ⟨{ name := "", cols := #[], affs := #[], colls := #[], base := 0, rowid := none, hidden := #[] }⟩

def SrcInfo.slots (s : SrcInfo) : Nat :=
  if !s.flat.isEmpty then 0 else if s.width > 0 then s.width else s.cols.size + (if s.rowid.isSome then 1 else 0)

structure Scope where
  srcs : Array SrcInfo := #[]
  deriving Inhabited

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
  /-- how many FROM items read each WITH table, by id -/
  cteReads : Array Nat := #[]
  /-- the deepest outer frame referred to since the last reset -/
  outer : Nat := 0

/-- A compile error: sqlite3's message, and the offset in the statement's text it points at when it has one. -/
structure CErr where
  msg : String
  pos : Option Nat := none

/-- A compile error with no offset. -/
def throwC {α : Type} {m : Type → Type} [MonadExcept CErr m] (msg : String) : m α := throw { msg }

abbrev CM := StateT CState (Except CErr)

def throwAt {α : Type} (pos : Option Nat) (msg : String) : CM α := throw { msg, pos }

/-- A compiled expression's affinity and collation (`true`: written with COLLATE). -/
abbrev Typed := CExpr × Aff × Option (Collation × Bool)

/-- The aggregate functions. -/
def aggNames : List String :=
  ["COUNT", "SUM", "TOTAL", "AVG", "MIN", "MAX", "GROUP_CONCAT", "STRING_AGG", "JSON_GROUP_ARRAY", "JSON_GROUP_OBJECT", "MEDIAN",
   "PERCENTILE", "PERCENTILE_CONT", "PERCENTILE_DISC"]

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

/-- Column `(tbl.)name` in one scope: its slot (`.slot`) or, in a FROM item read in place, the item and column
(`.ref`); its affinity and collation. -/
def resolveIn (sc : Scope) (tbl : Option String) (name : String) (pos : Option Nat := none) : Except CErr (Option (FlatCol × Aff × Collation)) := do
  let mut found : Option (FlatCol × Aff × Collation) := none
  let mut count := 0
  for s in sc.srcs do
    if let some t := tbl then
      unless nameEq s.name t do continue
    match s.cols.findIdx? (nameEq · name) with
    | some i =>
      if tbl.isNone && s.hidden.getD i false then continue
      let r : FlatCol := if s.flat.isEmpty then .slot (s.base + i) else .ref s i
      if found.isNone then found := some (r, s.affs.getD i .none, s.colls.getD i .binary)
      count := count + 1
    | none =>
      if (nameEq name "rowid" || nameEq name "oid" || nameEq name "_rowid_") then
        if let some r := s.rowid then
          if found.isNone then found := some (.slot r, .integer, .binary)
          count := count + 1
  if count > 1 && tbl.isNone then throw { msg := s!"ambiguous column name: {name}", pos : CErr }
  return found

def resolve (scopes : List Scope) (tbl : Option String) (name : String) (pos : Option Nat := none) (depth : Nat := 0) :
    Except CErr (Option (Nat × FlatCol × Aff × Collation)) :=
  match scopes with
  | [] => .ok none
  | sc :: rest => do
    match ← resolveIn sc tbl name pos with
    | some (s, a, c) => return some (depth, s, a, c)
    | none => resolve rest tbl name pos (depth + 1)

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

def stripCollate (e : Expr) : Expr := match e with | .collate x _ => x | x => x

/-- An ORDER BY term's direction, NULLs placement and collation (a result column's, unless it has COLLATE). -/
def dirOf (t : OrderTerm) (names : Array String) (colls : Array (Option (Collation × Bool))) : Bool × Bool × Collation :=
  match t with
  | .mk e desc nf =>
    let coll := match e with
      | .collate _ c => (Collation.ofName? c).getD .binary
      | e => match e with
        | .lit (.int k) => ((colls.getD (k.toNatClampNeg - 1) none).map (·.1)).getD .binary
        | .col _ n _ _ => match names.findIdx? (nameEq · n) with
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
  | .col _ n _ _ => names.findIdx? (nameEq · n)
  | _ => none
def orderTermColl (e : Expr) : Option Collation :=
  match e with
  | .collate _ c => Collation.ofName? c
  | _ => none
/-- a simple SELECT's ORDER BY term that is a plain column: its declared collation -/
def exprColl (env : CEnv) (core : Core) (e : Expr) : Option Collation :=
  match core, e with
  | .select _ _ (some (.table tn _)) [] _ _ _, .col _ n _ _ =>
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

/-- The number of arguments a window-only function takes (at least, at most). -/
def winArity (n : String) : Option (Nat × Nat) :=
  match n with
  | "ROW_NUMBER" | "RANK" | "DENSE_RANK" | "PERCENT_RANK" | "CUME_DIST" => some (0, 0)
  | "NTILE" | "FIRST_VALUE" | "LAST_VALUE" => some (1, 1)
  | "LAG" | "LEAD" => some (1, 3)
  | "NTH_VALUE" => some (2, 2)
  | _ => none

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

/-- Whether conjunct `c` pins column slot `s` to one value under collation `coll` (sqlite's where.c: a term `col IS NULL`,
`col = e` or `col IS e`, `e` reading no column of the item, makes an ORDER BY on the column hold on every row). -/
def pinsCol (s : Nat) (coll : Collation) (c : CExpr) : Bool :=
  let const (e : CExpr) : Bool := let (ss, corr) := slotsOf e 64; ss.isEmpty && !corr
  match c with
  | .isNull (.col 0 t) false => t == s
  | .cmp op (.col 0 t) e _ k => (op == .eq || op == .is) && t == s && const e && k == coll
  | .cmp op e (.col 0 t) _ k => (op == .eq || op == .is) && t == s && const e && k == coll
  | _ => false

/-- A join whose only aggregate is min() or max() of a column some WHERE term pins: the loop stops after its first row, so the
bare columns are that row's (sqlite3 stops the whole join once the pinned column's order is satisfied). The source holding the
column is read as `Access.ordered`, which for an aggregate core means the loop stops after one joined row. -/
def minMaxJoin : CCore → CCore
  | core@(.select srcs pre filters #[] gc none cols rcs order #[.mk name dist false #[.col 0 s] coll none] true d w #[]) =>
    if !(name == "MIN" || name == "MAX") || srcs.size < 2 || !(filters.any fun fs => fs.any (pinsCol s coll)) then core else
    let pick := (List.range srcs.size).find? fun i => match srcs[i]? with
      | some (CSource.table _ n _ _ _ base (.full) false false _ _) => base ≤ s && s < base + n
      | _ => false
    match pick with
    | some i =>
      match srcs[i]? with
      | some (CSource.table root n ipk rc dv base acc l r lay on) =>
        .select (srcs.setIfInBounds i (CSource.table root n ipk rc dv base (.ordered false acc) l r lay on)) pre filters #[] gc none cols rcs order
          #[.mk name dist false #[.col 0 s] coll none] true d w #[]
      | _ => core
    | none => core
  | core => core

/-- sqlite's min()/max() optimization (select.c minMaxQuery, where.c WHERE_ORDERBY_MIN/MAX): the only aggregate of a
one-table core with no GROUP BY, HAVING or FILTER is min() or max() of a column, an ORDER BY the loop may satisfy, and
the loop stops after its first row. The loop satisfies it when a WHERE term pins the column, or its access path gives
the column in order: the rowid, or an index led by the column (read backwards for max(); min() of a column that may be
NULL reads the index from its first non-NULL entry, which an ordered scan does not). The item is then read as
`Access.ordered`, which for an aggregate core means the loop stops after one joined row. -/
def minMaxCore (schema : Schema) : CCore → CCore
  | .select #[.table root n ipk rc dv base access false false layout on] pre filters #[] gc none cols rcs order
      #[.mk name dist false #[.col 0 s] coll none] true d w #[] =>
    let core := .select #[.table root n ipk rc dv base access false false layout on] pre filters #[] gc none cols rcs order
      #[.mk name dist false #[.col 0 s] coll none] true d w #[]
    let sel (a : Access CExpr) : CCore :=
      .select #[.table root n ipk rc dv base a false false layout on] pre filters #[] gc none cols rcs order
        #[.mk name dist false #[.col 0 s] coll none] true d w #[]
    let desc := name == "MAX"
    if !(name == "MIN" || name == "MAX") || !layout.isEmpty || !on.isEmpty || s < base || s > base + n then core
    else if (filters.getD 0 #[]).any (pinsCol s coll) then
      match access with
      | .full | .rowidRange .. | .index .. => sel (.ordered false access)
      | _ => core
    else
      let isRowid := s == base + n || ipk.map (base + ·) == some s
      let tbl := tableOfRoot schema root
      let canBeNull := !isRowid && !(tbl.bind (·.cols[s - base]?)).any (·.notNull)
      if !desc && canBeNull then core else
      -- (a scan of the whole table: the one index led by the column, read whole in its order. sqlite may drive the loop from
      -- another index when a WHERE term reads an index's leading column, or from a partial or expression index: left alone)
      let access := match access, tbl with
        | .full, some t =>
          let ixs := schema.indexesOfTable t
          let leads := ixs.map fun ix => base + ix.cols.getD 0 0
          let others := (filters.getD 0 #[]).any fun c => (slotsOf c 64).1.any leads.contains
          match ixs.filter fun ix => ix.cols[0]? == some (s - base) && ix.colls[0]? == some coll with
          | #[ix] =>
            if isRowid || others || ixs.any (fun ix => ix.pred.isSome || ix.hasExprs) then access
            else Access.index ix.root ix.keyInfo #[] none none
          | _ => access
        | a, _ => a
      match orderedItem schema true (.table root n ipk rc dv base access false false layout on) #[.col 0 s]
          #[(desc, !desc, coll)] with
      | some (.table _ _ _ _ _ _ a _ _ _ _) => sel a
      | _ => core
  | core => core

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

/-- EXISTS asks only whether a row comes: its result columns are never computed (sqlite3CodeSubselect). -/
def existsOnly : CSel → CSel
  | .mk ctes cores ops dirs limit offset n =>
    .mk ctes (cores.map fun c => match c with
      | .select srcs pre f g gc h _ _ order aggs isAgg d w ws => .select srcs pre f g gc h #[.lit (.int 1)] #[.binary] order aggs isAgg d w ws
      | c => c) ops dirs limit offset n

/-- A scalar or EXISTS subquery stops at one row: its LIMIT X becomes X <> 0 (as sqlite does), so X is a boolean there. -/
def oneRow : CSel → CSel
  | .mk ctes cores ops dirs limit offset n =>
    .mk ctes cores ops dirs (some ((limit.map fun e => CExpr.cmp .ne e (.lit (.int 0)) .numeric .binary).getD (.lit (.int 1)))) offset n

/-- Whether `p` holds at some node of an expression, not looking into its subqueries. -/
def exprAny (p : Expr → Bool) : Expr → Nat → Bool
  | _, 0 => false
  | e, fuel+1 => p e || match e with
    | .bin _ a b => exprAny p a fuel || exprAny p b fuel
    | .un _ a | .cast a _ | .collate a _ | .isNull a _ | .inSelect a _ _ => exprAny p a fuel
    | .fn _ _ _ args _ | .row args => args.any (exprAny p · fuel)
    | .case b ws els => (b.toList ++ ws.flatMap (fun (w, t) => [w, t]) ++ els.toList).any (exprAny p · fuel)
    | .between a lo hi _ => exprAny p a fuel || exprAny p lo fuel || exprAny p hi fuel
    | .inList a items _ => (a :: items).any (exprAny p · fuel)
    | .matches _ a pat esc _ => (a :: pat :: esc.toList).any (exprAny p · fuel)
    | .window _ _ _ args f (Window.mk part ord _) _ =>
      (args ++ f.toList ++ part ++ ord.map fun (OrderTerm.mk o _ _) => o).any (exprAny p · fuel)
    | _ => false

/-- An aggregate call (as compileExpr reads one: a FILTER rides as the last argument). -/
def isAggCall : Expr → Bool
  | .fn name _ star args0 _ =>
    let n := upperAscii name
    let args := match args0.getLast? with
      | some (.fn t _ _ [_] _) => if t == filterTag then args0.dropLast else args0
      | _ => args0
    isAggName n args.length star && (n != "MIN" && n != "MAX" || args.length == 1)
  | _ => false

/-- An aggregate other than count(), min() and max() (select.c SF_OrderByReqd: one that may read its rows' order). -/
def isOrderedAgg (e : Expr) : Bool :=
  isAggCall e && match e with
    | .fn name _ _ _ _ => !["COUNT", "MIN", "MAX"].contains (upperAscii name)
    | _ => false

def isWindowCall : Expr → Bool
  | .window .. => true
  | _ => false

/-- A function call or a subquery (select.c SF_ComplexResult: EP_HasFunc or EP_Subquery). -/
def isComplex : Expr → Bool
  | .fn .. | .window .. | .matches .. | .subquery _ | .exists .. | .inSelect .. => true
  | _ => false

def colsAny (p : Expr → Bool) (cols : List ResultCol) : Bool :=
  cols.any fun c => match c with
    | .expr e _ _ => exprAny p e 64
    | _ => false

def termsAny (p : Expr → Bool) (terms : List OrderTerm) : Bool :=
  terms.any fun (.mk e _ _) => exprAny p e 64

/-- What select.c flattenSubquery reads of the SELECT a FROM item belongs to: aggregate, DISTINCT, a window, a result
column with a function or subquery, an aggregate that may read order, its FROM item count (once merged ones are
counted), a WHERE (ON terms are WHERE terms to sqlite), ORDER BY (each term a number or a name: (18)), LIMIT, whether
it is an arm of a compound, may not become one (the recursive part of a WITH table: (23)), has a RIGHT or FULL JOIN, or
has an ORDER BY or LIMIT from an item read in place (which a UNION ALL read in place would have to carry). -/
structure Shape where
  agg : Bool := false
  distinct : Bool := false
  win : Bool := false
  complex : Bool := false
  orderReqd : Bool := false
  nsrc : Nat := 0
  hasWhere : Bool := false
  hasOrder : Bool := false
  orderCols : Bool := true
  hasLimit : Bool := false
  compound : Bool := false
  noCompound : Bool := false
  hasRight : Bool := false
  handed : Bool := false

/-- One arm of a subquery as flattenSubquery's conditions read it (none: a VALUES, or no FROM clause). -/
structure CoreFacts where
  distinct : Bool
  agg : Bool
  win : Bool
  right : Bool
  nitems : Nat
  /-- a WHERE or an ON/USING term -/
  hasWhere : Bool
  /-- its only FROM item, when it has no joins -/
  only : Option FromItem

def coreFacts (orderBy : List OrderTerm) : Core → Option CoreFacts
  | .values _ => none
  | .select _ _ none _ _ _ _ => none
  | .select d cols (some f) js w g h =>
    some { distinct := d, agg := !g.isEmpty || h.isSome || colsAny isAggCall cols || termsAny isAggCall orderBy,
           win := colsAny isWindowCall cols || termsAny isWindowCall orderBy,
           right := js.any fun (.mk k _ _ _) => k == .right || k == .full,
           nitems := 1 + js.length,
           hasWhere := w.isSome || js.any fun (.mk _ _ on u) => on.isSome || !u.isEmpty,
           only := if js.isEmpty then some f else none }

/-- A FROM item that may be read in place: its SELECT, the environment its WITH and FROM clauses compile in, how many
empty scopes stand for the levels between its definition and this FROM clause (a WITH table read from a deeper SELECT,
or a view, which sees none), the column names it is read under (a WITH table's or view's column list), its name, and
the WITH table it is (whose read is counted), or the view. -/
structure FlatSrc where
  q : Select
  env : CEnv
  pad : Nat := 0
  names : Option (Array String) := none
  alias : String
  cte : Option Nat := none
  /-- the view it is (its errors point nowhere in the statement's text) -/
  view : Option String := none

def bumpRead (reads : Array Nat) (id : Nat) : Array Nat :=
  (if reads.size ≤ id then reads ++ Array.replicate (id + 1 - reads.size) 0 else reads).modify id (· + 1)

/-- whether a FROM item names a rowid table (not a WITH table of `ctes` or `env`, nor a view) -/
def rowidTable (env : CEnv) (ctes : List Cte) : Option FromItem → Bool
  | some (.table qname _) =>
    let name := (Schema.splitQual qname).2
    !(ctes.any fun (Cte.mk n _ _ _) => nameEq n name) && !(env.ctes.any (nameEq ·.name name)) &&
      match env.schema.table? qname with
      | some t => !t.withoutRowid
      | none => false
  | _ => false

/-- A FROM item that a SELECT may read in place: a subquery, a view, or a WITH table that is not recursive or
MATERIALIZED. -/
def flatSrc (env : CEnv) : FromItem → Option FlatSrc
  | .subquery q alias => some { q, env, alias := alias.getD "" }
  | .table qname alias =>
    let name := (Schema.splitQual qname).2
    match env.ctes.findIdx? (nameEq ·.name name) with
    | some idx => (env.ctes[idx]?).bind fun c => c.body.map fun q =>
        let δ := env.scopes.length - c.nscopes
        { q, env := { env with ctes := env.ctes.drop (idx + 1), scopes := List.replicate δ {} ++ env.scopes.drop δ, aliases := [] },
          pad := δ, names := some c.cols, alias := alias.getD name, cte := some c.id }
    | none => (env.schema.view? qname).map fun v =>
        { q := v.q, env := { env with scopes := [], aliases := [] }, pad := env.scopes.length,
          names := if v.cols.isEmpty then none else some v.cols.toArray, alias := alias.getD name, view := some v.name }
  | _ => none

/-- One arm of a UNION ALL read in place: its number, and the compound's column names, affinities and collations. -/
abbrev Arm := Nat × Array String × Array Aff × Array (Option (Collation × Bool))

/-- What a merge hands the SELECT it is merged into: the shape after it, the WHERE conjuncts of the items read in place
(by the index of the source they belong to: ON terms when it is a LEFT JOIN's), an ORDER BY (its keys and directions)
and a LIMIT, their own WITH tables (with MATERIALIZED as written), and, when a UNION ALL subquery is to be read in place,
its arm count and its column names, affinities and collations; the arms chosen for the UNION ALLs read in place
after these items. -/
structure FlatOut where
  shape : Shape := {}
  conds : Array (Nat × CExpr) := #[]
  order : Option (Array CExpr × Array (Bool × Bool × Collation)) := none
  limit : Option CExpr := none
  ctes : Array (CCte × Option Bool) := #[]
  fork : Option (Nat × Array String × Array Aff × Array (Option (Collation × Bool))) := none
  arms : List Arm := []
  deriving Inhabited

/-- A FROM item as compileFrom reads it: its join, the item, ON, USING. -/
abbrev FromIn := JoinKind × FromItem × Option Expr × List String

/-- How flattenSubquery reads a FROM item: not in place, in place (dropping its ORDER BY when tag-select-0230 omits it),
or, a UNION ALL, once per arm (its arm count, column names, affinities, collations). -/
inductive FlatPlan where
  | no
  | simple (dropOrder : Bool)
  | compound (n : Nat) (names : Array String) (affs : Array Aff) (colls : Array (Option (Collation × Bool)))

def CSource.base : CSource → Nat
  | .table _ _ _ _ _ base .. | .sub _ _ base .. | .cte _ _ base .. | .tvf _ _ _ base .. => base

/-- The source with a LEFT JOIN's missing row: NULLs when no row matches. -/
def CSource.setLeft : CSource → CSource
  | .table root n ipk rc dv base acc _ right layout on => .table root n ipk rc dv base acc true right layout on
  | .sub q n base _ right on keys => .sub q n base true right on keys
  | .cte id n base _ right on keys => .cte id n base true right on keys
  | .tvf f args n base _ right on => .tvf f args n base true right on

/-- A core that reads the rows of `cores` (UNION ALL) as a subquery: a UNION ALL read in place after UNION, INTERSECT or
EXCEPT stays one arm. -/
def passThrough (cores : Array CCore) (n : Nat) (rcolls : Array Collation) : CCore :=
  .select #[.sub (.mk #[] cores (Array.replicate (cores.size - 1) .unionAll) #[] none none n) n 0 false false #[] #[]] #[]
    #[#[]] #[] #[] none ((List.range n).toArray.map (.col 0 ·)) rcolls #[] #[] false false n #[]

mutual
def compileExpr (env : CEnv) : Expr → Nat → CM Typed
  | _, 0 => throwC "expression nested too deeply"
  | e, fuel+1 => match e with
  | .lit v => return (.lit v, .none, none)
  | .col tbl name _ pos => do
    match ← liftM (resolve env.scopes tbl name pos) with
    | some (d, .ref si i, a, c) => return (← compileFlatCol env (.ref si i) d (env.scopes.drop (d + 1)) fuel, a, some (c, false))
    | some (_, .expr _, a, c) => return (.lit .null, a, some (c, false))
    | some (d, .slot s, a, c) =>
      modify fun st => { st with outer := max st.outer d }
      let isJsonValue := ((env.scopes.drop d).head?.map fun sc => sc.srcs.any fun si => si.jsonEach && si.base + 1 == s).getD false
      if isJsonValue then return (.fn jsonValueTag #[.col d s, .col d (s + 1)], a, some (c, false))
      return (.col d s, a, some (c, false))
    | none =>
      match tbl, env.aliases.find? (nameEq ·.1 name) with
      | none, some (_, e) => compileExpr { env with aliases := [] } e fuel
      | _, _ => throwAt pos (match tbl with | some t => s!"no such column: {t}.{name}" | none => s!"no such column: {name}")
  | .bin op (.row as) (.row bs) => do
    if as.length != bs.length then throwC "row value misused"
    if !([BinOp.eq, .ne, .lt, .le, .gt, .ge, .is, .isNot].contains op) then throwC "row value misused"
    compileExpr env (rowCmp op as bs (as.length + 1)) fuel
  | .bin _ (.row _) _ | .bin _ _ (.row _) => throwC "row value misused"
  | .row _ => throwC "row value misused"
  | .between (.row es) (.row lo) (.row hi) neg => do
    if es.length != lo.length || es.length != hi.length then throwC "row value misused"
    let r := Expr.bin .and (rowCmp .ge es lo (es.length + 1)) (rowCmp .le es hi (es.length + 1))
    compileExpr env (if neg then .un .not r else r) fuel
  | .inList (.row es) items neg => do
    let eqs ← items.mapM fun it => match it with
      | .row xs => if xs.length == es.length then pure (rowCmp .eq es xs (es.length + 1)) else throwC "row value misused"
      | _ => throwC "row value misused"
    let any := eqs.foldr (fun e acc => Expr.bin .or e acc) (.lit (.int 0))
    compileExpr env (if neg then .un .not any else any) fuel
  | .inSelect (.row es) q neg => do
    let ces ← compileList env es fuel
    let (cq, _, affs, colls, _) ← compileSub env q false fuel
    if cq.ncols != ces.size then throwC s!"sub-select returns {cq.ncols} columns - expected {ces.size}"
    let aff := ces.mapIdx fun i (t : Typed) => cmpAff t.2.1 (affs.getD i .none)
    let coll := ces.mapIdx fun i (t : Typed) => cmpColl t.2.2 (colls.getD i none)
    return (.inSelRow (ces.map fun (t : Typed) => t.1) cq neg aff coll, .none, none)
  | .raise k m => return (.raise k m, .none, none)
  | .window name distinct star args filter (.mk partition orderBy frame) pos => do
    let n := upperAscii name
    let st ← get
    unless st.allowWin do throwAt pos s!"misuse of window function {name}()"
    unless winNames.contains n do throwC s!"{name}() may not be used as a window function"
    if let some (lo, hi) := winArity n then
      if args.length < lo || args.length > hi || star then throwAt pos s!"wrong number of arguments to function {name}()"
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
  | .fn name distinct star args0 pos => do
    let n := upperAscii name
    -- an aggregate's FILTER clause rides as the last argument
    let (args, flt) := match args0.getLast? with
      | some (.fn t _ _ [f] _) => if t == filterTag then (args0.dropLast, some f) else (args0, none)
      | _ => (args0, none)
    if isAggName n args.length star && (n != "MIN" && n != "MAX" || args.length == 1) then
      let st ← get
      unless st.allowAgg do throwAt pos s!"misuse of aggregate function {name}()"
      if distinct && args.length != 1 then throwC "DISTINCT aggregates must have exactly one argument"
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
    else if flt.isSome then throwC s!"FILTER may not be used with non-aggregate {name}()"
    else
      -- the arguments resolve first: a column that does not exist is the error before a function that does not
      let cargs ← compileList env args fuel
      match scalarArity n with
      | none =>
        -- an aggregate or window function called with arguments it does not take, or outside its clause
        if aggNames.contains n then throwAt pos s!"wrong number of arguments to function {name}()"
        else match winArity n with
          | some (lo, hi) =>
            if args.length < lo || args.length > hi || star then throwAt pos s!"wrong number of arguments to function {name}()"
            else throwAt pos s!"misuse of window function {name}()"
          | none => throwAt pos s!"no such function: {name}"
      | some (lo, hi) =>
        if args.length < lo || (match hi with | some h => args.length > h | none => false) || star then
          throwAt pos s!"wrong number of arguments to function {name}()"
        if distinct then throwC s!"DISTINCT aggregates must have exactly one argument"
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
    | none => throwC s!"no such collation sequence: {c}"
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
    let (cq, _, affs, _, corr) ← compileSub env q false fuel
    if cq.ncols != 1 then throwC s!"sub-select returns {cq.ncols} columns - expected 1"
    return (.inSel ce cq neg (cmpAff ae (affs.getD 0 .none)) (cmpColl ke none) corr, .none, none)
  | .matches op e p esc neg => do
    let (ce, _, _) ← compileExpr env e fuel
    let (cp, _, _) ← compileExpr env p fuel
    let cesc ← match esc with
      | some x => do let r ← compileExpr env x fuel; pure (some r.1)
      | none => pure none
    if op == .regexp || op == .match then throwC s!"no such function: {if op == .regexp then "REGEXP" else "MATCH"}"
    return (.matchE op ce cp cesc neg, .none, none)
  | .isNull e neg => do
    let (ce, _, _) ← compileExpr env e fuel
    return (.isNull ce neg, .none, none)
  | .exists q neg => do
    let (cq, _, _, _, corr) ← compileSub env q false fuel
    return (.exists (existsOnly (oneRow cq)) neg corr, .none, none)
  | .subquery q => do
    let (cq, _, affs, colls, corr) ← compileSub env q false fuel
    if cq.ncols != 1 then throwC s!"sub-select returns {cq.ncols} columns - expected 1"
    return (.scalar (oneRow cq) corr, affs.getD 0 .none, (colls.getD 0 none))
  | .param t => throwC s!"lean-sqlite: parameters are not supported: {t}"
termination_by structural _ fuel => fuel

def compileList (env : CEnv) : List Expr → Nat → CM (Array Typed)
  | [], _ => return #[]
  | _, 0 => throwC "expression nested too deeply"
  | e :: rest, fuel+1 => do
    let c ← compileExpr env e fuel
    let cs ← compileList env rest fuel
    return #[c] ++ cs
termination_by structural _ fuel => fuel

def compilePairs (env : CEnv) : List (Expr × Expr) → Nat → CM (Array (CExpr × CExpr))
  | [], _ => return #[]
  | _, 0 => throwC "expression nested too deeply"
  | (a, b) :: rest, fuel+1 => do
    let (ca, _, _) ← compileExpr env a fuel
    let (cb, _, _) ← compileExpr env b fuel
    let cs ← compilePairs env rest fuel
    return #[(ca, cb)] ++ cs
termination_by structural _ fuel => fuel

/-- A subquery: compiled with its own aggregates, and whether it reads the enclosing rows. `inFrom`: a FROM item of the
enclosing SELECT, whose own scope its `env` lacks (so its depth `d` is the enclosing SELECT's depth `d`, not `d - 1`). -/
def compileSub (env : CEnv) (q : Select) (inFrom : Bool) : Nat → CM (CSel × Array String × Array Aff × Array (Option (Collation × Bool)) × Bool)
  | 0 => throwC "expression nested too deeply"
  | fuel+1 => do
    let st ← get
    set { st with aggs := #[], allowAgg := false, wins := #[], allowWin := false, outer := 0 }
    let (cq, names, affs, colls) ← compileSelect env q fuel
    let st2 ← get
    set { st2 with aggs := st.aggs, allowAgg := st.allowAgg, wins := st.wins, allowWin := st.allowWin,
                   outer := max st.outer (st2.outer - (if inFrom then 0 else 1)) }
    return (cq, names, affs, colls, st2.outer ≥ 1)
termination_by structural fuel => fuel

/-- A SELECT: its WITH tables, cores, ORDER BY and LIMIT; also its column names, affinities and collations. -/
def compileSelect (env : CEnv) : Select → Nat → CM (CSel × Array String × Array Aff × Array (Option (Collation × Bool)))
  | _, 0 => throwC "query nested too deeply"
  | q, fuel+1 => compileSelectIn env false q fuel
termination_by structural _ fuel => fuel

/-- compileSelect; `recursive`: the SELECT of a recursive WITH table, whose cores read no UNION ALL in place. -/
def compileSelectIn (env : CEnv) (recursive : Bool) : Select → Nat →
    CM (CSel × Array String × Array Aff × Array (Option (Collation × Bool)))
  | _, 0 => throwC "query nested too deeply"
  | .mk rec ctes first rest orderBy limit offset, fuel+1 => do
    -- WITH tables, each visible to the later ones (and a recursive one to itself)
    let (env, cctes) ← compileCtes env rec ctes fuel
    let lim := limit.isSome
    let st0 ← get
    let r0 ← compileCore env first (if rest.isEmpty then some orderBy else none) (!rest.isEmpty) lim recursive fuel
    -- a SELECT read as a UNION ALL takes a compound's ORDER BY, which names result columns (flattenSubquery (18))
    let (cs0, names, affs, colls, fo0) ← if rest.isEmpty && r0.1.size > 1
        && !orderBy.all (fun (.mk e _ _) => (orderTermColumn e r0.2.1).isSome) then do
        set st0
        compileCore env first (some orderBy) false lim true fuel
      else pure r0
    let rcolls := colls.map fun k => (k.map (·.1)).getD .binary
    let mut cores := cs0
    let mut ops : Array CompoundOp := Array.replicate (cs0.size - 1) .unionAll
    let mut hoisted := fo0.ctes
    for (op, core) in rest do
      let (cs, ns, _, _, fo) ← compileCore env core none true lim recursive fuel
      if ns.size != names.size then
        throwC s!"SELECTs to the left and right of {opName op} do not have the same number of result columns"
      hoisted := hoisted ++ fo.ctes
      -- an arm read as a UNION ALL: its cores, unless another operator would take only the first of them
      if cs.size > 1 && op != .unionAll then
        cores := cores.push (passThrough cs ns.size rcolls)
        ops := ops.push op
      else
        cores := cores ++ cs
        ops := ops.push op ++ Array.replicate (cs.size - 1) .unionAll
    let single := cores.size == 1
    -- a compound's ORDER BY names result columns
    if !single && !orderBy.isEmpty then
      let mut ks : Array Nat := #[]
      let mut i := 0
      for .mk e _ _ in orderBy do
        i := i + 1
        let k ← match orderTermColumn e names with
          | some k => pure k
          | none => throwC s!"{ordinalName i} ORDER BY term does not match any column in the result set"
        ks := ks.push k
      cores := cores.map fun c => match c with
        | .select srcs pre f g gc h cols rc _ aggs isAgg d w ws => .select srcs pre f g gc h cols rc (ks.map (cols.getD · default)) aggs isAgg d w ws
        | .values rows _ => .values rows ks
    cores := cores.map (minMaxJoin ∘ minMaxCore env.schema)
    let dirs := orderBy.toArray.map fun (t : OrderTerm) => dirOf t names colls
    -- a plain column's collation for ORDER BY in a simple select; with none, a subquery read in place may give one
    let dirs := if !single then dirs else if orderBy.isEmpty then ((fo0.order.map (·.2)).getD #[]) else dirs.mapIdx fun i d =>
        let (desc, nf, coll) := d
        match orderBy[i]? with
        | some (.mk e _ _) => if (orderTermColl e).isSome then d else
          match exprColl env first e with
          | some c => (desc, nf, c)
          | none => (desc, nf, coll)
        | none => d
    -- a simple SELECT whose first FROM item's access path gives the ORDER BY needs no sort
    let (cores', dirs) := match cores[0]?, single with
      | some (.select srcs pre f g gc h cols rc order aggs false false w #[]), true =>
        if g.isEmpty && !srcs.any isRightOuter then
          match srcs[0]?.bind fun s => orderedItem env.schema (srcs.size == 1) s order dirs with
          | some s0 => (#[CCore.select (srcs.setIfInBounds 0 s0) pre f g gc h cols rc #[] aggs false false w #[]], #[])
          | none => (cores, dirs)
        else (cores, dirs)
      -- a grouped SELECT comes out in its GROUP BY keys' order: an ORDER BY of those keys, ascending, needs no sort
      | some (.select srcs pre f g gc h cols rc _ aggs true false w #[]), true =>
        let groupBy := match first with | .select _ _ _ _ _ gb _ => gb | _ => []
        let sameRef (a b : Expr) : Bool := match a, b with
          | .col t1 n1 _ _, .col t2 n2 _ _ => nameEq n1 n2 && (match t1, t2 with | none, none => true | some x, some y => nameEq x y | _, _ => false)
          | _, _ => false
        let byKeys := !g.isEmpty && !orderBy.isEmpty && orderBy.length ≤ groupBy.length &&
          (orderBy.zip groupBy).all fun (o, k) => match o with
            | .mk e false none => sameRef e k
            | _ => false
        if byKeys then (#[CCore.select srcs pre f g gc h cols rc #[] aggs true false w #[]], #[]) else (cores, dirs)
      | _, _ => (cores, dirs)
    cores := cores'
    let cl ← match limit with
      | some e => do let r ← compileExpr { env with scopes := env.scopes } e fuel; pure (some r.1)
      | none => pure (if single then fo0.limit else none)
    let co ← match offset with
      | some e => do let r ← compileExpr env e fuel; pure (some r.1)
      | none => pure none
    -- a WITH table more than one FROM item reads is computed once, unless NOT MATERIALIZED
    let reads := (← get).cteReads
    let own : Array (CCte × Option Bool) := (cctes.zip ctes.toArray).map fun (c, Cte.mk _ _ _ written) => (c, written)
    let cctes := (own ++ hoisted).map fun (CCte.mk id q r m, written) =>
      CCte.mk id q r (m || (written != some false && reads.getD id 0 ≥ 2))
    return (.mk cctes cores ops dirs cl co names.size, names, affs, colls)
termination_by structural _ fuel => fuel

def compileCtes (env : CEnv) (recursive : Bool) : List Cte → Nat → CM (CEnv × Array CCte)
  | [], _ => return (env, #[])
  | _, 0 => throwC "query nested too deeply"
  | .mk name cols q materialized :: rest, fuel+1 => do
    let st ← get
    let id := st.nextCte
    set { st with nextCte := id + 1 }
    let selfRef := recursive && selectReads q name
    let (cq, info) ← if selfRef then do
        -- the initial SELECT gives the column names; then the whole query is compiled with the table visible
        let .mk r c first rest2 _ _ _ := q
        -- (the initial SELECT is compiled again with the rest: the WITH tables it reads are counted then)
        let reads := (← get).cteReads
        let (_, ns, affs, _) ← compileSelect env (.mk r c first [] [] none none) fuel
        modify fun st => { st with cteReads := reads }
        let ns := if cols.isEmpty then ns else cols.toArray
        let info : CteInfo := { name, id, cols := ns, affs := affs.map fun _ => .none }
        let env2 := { env with ctes := { info with queue := true } :: env.ctes }
        if rest2.length != 1 then throwC s!"lean-sqlite: recursive table {name} must be one SELECT UNION [ALL] one SELECT"
        let (cq, _, _, _) ← compileSelectIn env2 true q fuel
        pure (cq, info)
      else do
        let (cq, ns, affs, _) ← compileSelect env q fuel
        if !cols.isEmpty && cols.length != ns.size then
          throwC s!"table {name} has {ns.size} values for {cols.length} columns"
        let ns := if cols.isEmpty then ns else cols.toArray
        let body := if materialized == some true then none else some q
        pure (cq, { name, id, cols := ns, affs, body, nscopes := env.scopes.length : CteInfo })
    let env := { env with ctes := info :: env.ctes }
    let (env, more) ← compileCtes env recursive rest fuel
    return (env, #[.mk id cq selfRef (materialized == some true)] ++ more)
termination_by structural _ fuel => fuel

/-- One core: FROM, WHERE, GROUP BY, HAVING and the result columns (and, for a simple SELECT, ORDER BY). `arm`: it is
an arm of a compound; `limited`: its SELECT has a LIMIT; `recursive`: it is part of a recursive WITH table's
SELECT. A UNION ALL subquery read in place makes it several cores, one per arm, joined by UNION ALL; the last result is
what the subqueries read in place hand its SELECT (an ORDER BY, a LIMIT, their WITH tables). -/
def compileCore (env : CEnv) (core : Core) (orderBy : Option (List OrderTerm)) (arm limited recursive : Bool) :
    Nat → CM (Array CCore × Array String × Array Aff × Array (Option (Collation × Bool)) × FlatOut)
  | 0 => throwC "query nested too deeply"
  | fuel+1 => match core with
  | .values rows => do
    let mut crows := #[]
    let mut affs := #[]
    for r in rows do
      let cr ← compileList env r fuel
      if !crows.isEmpty && cr.size != (crows.getD 0 #[]).size then throwC "all VALUES must have the same number of terms"
      crows := crows.push (cr.map fun (t : Typed) => t.1)
      if affs.isEmpty then affs := cr.map fun _ => Aff.none
    let n := (crows.getD 0 #[]).size
    let names := (List.range n).toArray.map fun i => s!"column{i+1}"
    let order ← match orderBy with
      | some terms => terms.toArray.mapM fun (.mk e _ _) => match orderTermColumn e names with
        | some k => pure k
        | none => throwC "1st ORDER BY term does not match any column in the result set"
      | none => pure #[]
    return (#[.values crows order], names, affs, names.map fun _ => none, {})
  | .select distinct cols fromItem joins whereE groupBy having => do
    let items : Array FromIn := ((match fromItem with | some f => [(JoinKind.inner, f, none, [])] | none => [])
      ++ joins.map fun (.mk k it on u) => (k, it, on, u)).toArray
    let terms := orderBy.getD []
    let shape : Shape := {
      agg := !groupBy.isEmpty || colsAny isAggCall cols || having.any (exprAny isAggCall · 64) || termsAny isAggCall terms
      distinct, win := colsAny isWindowCall cols || termsAny isWindowCall terms, complex := colsAny isComplex cols
      orderReqd := colsAny isOrderedAgg cols || having.any (exprAny isOrderedAgg · 64) || termsAny isOrderedAgg terms
      nsrc := items.size
      hasWhere := whereE.isSome || joins.any fun (.mk _ _ on u) => on.isSome || !u.isEmpty
      hasOrder := !terms.isEmpty
      orderCols := terms.all fun (.mk e _ _) => match stripCollate e with | .lit (.int _) | .col none _ _ _ => true | _ => false
      hasLimit := limited, compound := arm, noCompound := recursive
      hasRight := joins.any fun (.mk k _ _ _) => k == .right || k == .full }
    compileSelectCore env distinct cols whereE groupBy having orderBy shape [] items fuel
termination_by structural fuel => fuel

/-- A SELECT core over its FROM items (compileCore). When one of them is a UNION ALL subquery read in place, the core is
compiled once for each of its arms (select.c flattenSubquery's compound-subquery flattening); `arms`: the arms
chosen so far, in the order the FROM items read in place meet them. -/
def compileSelectCore (env : CEnv) (distinct : Bool) (cols : List ResultCol) (whereE : Option Expr) (groupBy : List Expr)
    (having : Option Expr) (orderBy : Option (List OrderTerm)) (shape : Shape) (arms : List Arm) (items : Array FromIn) :
    Nat → CM (Array CCore × Array String × Array Aff × Array (Option (Collation × Bool)) × FlatOut)
  | 0 => throwC "query nested too deeply"
  | fuel+1 => do
    let st0 ← get
    -- the FROM items and their slots
    let (srcs, infos, onConds, width, fo) ← compileFrom env shape 0 0 none arms items fuel
    if let some (n, ns, as, cs) := fo.fork then
      set st0
      let mut cores := #[]
      let mut first : Option (Array String × Array Aff × Array (Option (Collation × Bool))) := none
      let mut ctes := #[]
      let mut reads : Option (Array Nat) := none
      for k in [0:n] do
        let (cs', names, affs, colls, x) ← compileSelectCore env distinct cols whereE groupBy having orderBy
          { shape with compound := true } (arms ++ [(k, ns, as, cs)]) items fuel
        -- (the copies read a WITH table as the one FROM item they copy)
        match reads with
        | some r => modify fun st => { st with cteReads := r }
        | none => reads := some (← get).cteReads
        cores := cores ++ cs'
        ctes := ctes ++ x.ctes
        if first.isNone then first := some (names, affs, colls)
      let (names, affs, colls) := first.getD (#[], #[], #[])
      return (cores, names, affs, colls, { ctes })
    let scope : Scope := { srcs := infos }
    let env' := { env with scopes := scope :: env.scopes }
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
        if infos.isEmpty then throwC "no tables specified"
        for s in infos do
          for i in [0:s.cols.size] do
            unless s.hidden.getD i false do
              ccols := ccols.push (← if s.flat.isEmpty then pure (.col 0 (s.base + i)) else compileFlatCol env (.ref s i) 0 env.scopes fuel)
              names := names.push (s.cols.getD i "")
              affs := affs.push (s.affs.getD i .none); colls := colls.push (some (s.colls.getD i .binary, false))
      | .tableStar t =>
        match infos.find? (nameEq ·.name t) with
        | none => throwC s!"no such table: {t}"
        | some s =>
          for i in [0:s.cols.size] do
            ccols := ccols.push (← if s.flat.isEmpty then pure (.col 0 (s.base + i)) else compileFlatCol env (.ref s i) 0 env.scopes fuel)
            names := names.push (s.cols.getD i "")
            affs := affs.push (s.affs.getD i .none); colls := colls.push (some (s.colls.getD i .binary, false))
      | .expr e alias span =>
        let (ce, a, k) ← compileExpr env' e fuel
        ccols := ccols.push ce; affs := affs.push a; colls := colls.push k
        names := names.push (match alias with
          | some n => n
          | none => match e with
            | .col tbl n _ _ =>
              -- the name of the column it resolved to (the slot of an item's column), else as colName finds it
              let resolved := match ce with
                | .col 0 s => infos.findSome? fun i => if i.base ≤ s then i.cols[s - i.base]? else none
                | _ => none
              match resolved with
              | some c => c
              | none => colName infos tbl n
            | _ => span)
    -- WHERE (no aggregates, no windows), ON
    modify fun st => { st with allowAgg := false, allowWin := false }
    -- HAVING needs aggregates in the result columns or a GROUP BY (one in HAVING itself does not count)
    if having.isSome && groupBy.isEmpty && (← get).aggs.isEmpty then throwC "HAVING clause on a non-aggregate query"
    let aliasList := cols.filterMap fun | .expr e (some a) _ => some (a, e) | _ => none
    let env' := { env' with aliases := aliasList }
    let whereConds ← compileList env' (match whereE with | some w => conjuncts w 64 | none => []) fuel
    -- GROUP BY: a number or an alias names a result column
    let mut cgroup : Array CExpr := #[]
    let mut gcolls : Array Collation := #[]
    for g in groupBy do
      match g with
      | .lit (.int k) =>
        if k < 1 || k.toNatClampNeg > ccols.size then throwC s!"{ordinalName cgroup.size.succ} GROUP BY term out of range - should be between 1 and {ccols.size}"
        cgroup := cgroup.push (ccols.getD (k.toNatClampNeg - 1) default)
        gcolls := gcolls.push (((colls.getD (k.toNatClampNeg - 1) none).map (·.1)).getD .binary)
      | _ =>
        let (c, _, k) ← try compileExpr env' g fuel catch e =>
          if e.msg.startsWith "misuse of aggregate function" then throwC "aggregate functions are not allowed in the GROUP BY clause" else throw e
        cgroup := cgroup.push c
        gcolls := gcolls.push ((k.map (·.1)).getD .binary)
    modify fun st => { st with allowAgg := true }
    let chaving ← match having with
      | some h => do let r ← compileExpr env' h fuel; pure (some r.1)
      | none => pure none
    -- ORDER BY of a simple SELECT: a number or an alias names a result column, else an expression over the FROM items;
    -- with none, a subquery read in place may hand it its own
    modify fun st => { st with allowWin := true }
    let corder ← match orderBy with
      | none | some [] => pure ((fo.order.map (·.1)).getD #[])
      | some terms => do
        let mut out := #[]
        let mut i := 0
        for .mk e _ _ in terms do
          i := i + 1
          let e0 := stripCollate e
          match e0 with
          | .lit (.int k) =>
            if k < 1 || k.toNatClampNeg > ccols.size then
              throwC s!"{ordinalName i} ORDER BY term out of range - should be between 1 and {ccols.size}"
            out := out.push (ccols.getD (k.toNatClampNeg - 1) default)
          | .col none n _ _ =>
            match cols.findIdx? (fun | .expr _ (some a) _ => nameEq a n | _ => false) with
            | some j => out := out.push (ccols.getD j default)
            | none => let (c, _, _) ← compileExpr env' e0 fuel; out := out.push c
          | _ => let (c, _, _) ← compileExpr env' e0 fuel; out := out.push c
        pure out
    let st ← get
    let aggs := st.aggs
    let wins := st.wins
    set { st with aggs := #[], allowAgg := false, wins := #[], allowWin := false }
    if !aggs.isEmpty && infos.isEmpty && false then throwC ""
    let isAgg := !aggs.isEmpty || !cgroup.isEmpty
    -- where each condition is checked, and how each table is read
    let bases := srcs.map (·.base)
    if (srcs.filter isRightOuter).size > 1 then throwC "lean-sqlite: only one RIGHT or FULL JOIN per SELECT is supported"
    -- (the WHERE of a subquery read in place comes first, as flattenSubquery puts it)
    let inner (jc : Nat × CExpr) : Option CExpr := if isOuter (srcs.getD jc.1 default) then none else some jc.2
    let allConds := fo.conds.filterMap inner ++ whereConds.map (fun (t : Typed) => t.1) ++ onConds.filterMap inner
    let leftOn : Array (Array CExpr) := (List.range srcs.size).toArray.map fun j =>
      ((fo.conds ++ onConds).filter fun (k, _) => k == j).map (·.2) |>.filter fun _ => isOuter (srcs.getD j default)
    let level (c : CExpr) : Option Nat :=
      let (ss, corr) := slotsOf c 64
      if corr then some (srcs.size - 1) else
      ss.foldl (fun (acc : Option Nat) s => let j := srcOfSlot bases s; some (max (acc.getD 0) j)) none
    let levels := allConds.map fun c => (c, level c)
    let pre := levels.filterMap fun (c, l) => if l.isNone || srcs.isEmpty then some c else none
    let filters := (List.range srcs.size).toArray.map fun j =>
      levels.filterMap fun (c, l) => if l == some j then some c else none
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
    -- an inner item read whole gets a transient index, unless each earlier item gives one row (a rowid lookup); a
    -- recursive WITH table's queue row is one row, not indexed, but its runs share the indexes of the other items
    let oneRow (s : CSource) : Bool := s matches .table _ _ _ _ _ _ (.rowidEq _) _ _ _ _
    let isQueue (s : CSource) : Bool := match s with
      | .cte id .. => env.ctes.any fun c => c.id == id && c.queue
      | _ => false
    let srcs : Array CSource := if srcs.size < 2 then srcs else srcs.mapIdx fun j s =>
      if j == 0 || isQueue s || (srcs.extract 0 j).all oneRow then s else
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
    return (#[.select srcs pre filters cgroup gcolls chaving ccols rcolls corder aggs isAgg distinct width wins], names, affs, colls,
      { order := match orderBy with | none | some [] => fo.order | _ => none, limit := fo.limit, ctes := fo.ctes })
termination_by structural fuel => fuel


/-- A FROM item read as a source: a table, view, WITH table, subquery or table-valued function at slot `slot`
(`infos`: the earlier items, whose columns a table-valued function's arguments may name). -/
def compileItem (env : CEnv) (infos : Array SrcInfo) (item : FromItem) (slot : Nat) (left right : Bool) :
    Nat → CM (CSource × SrcInfo)
  | 0 => throwC "query nested too deeply"
  | fuel+1 => do
    match item with
        | .table qname alias =>
          let name := (Schema.splitQual qname).2
          let an := alias.getD name
          match env.ctes.find? (nameEq ·.name name) with
          | some c =>
            unless c.queue do
              modify fun st => { st with cteReads := (if st.cteReads.size ≤ c.id then
                st.cteReads ++ Array.replicate (c.id + 1 - st.cteReads.size) 0 else st.cteReads).modify c.id (· + 1) }
            pure (CSource.cte c.id c.cols.size slot left right #[] #[],
              { name := an, cols := c.cols, affs := c.affs, colls := c.cols.map fun _ => .binary, base := slot,
                rowid := none : SrcInfo })
          | none =>
          match env.schema.view? qname with
          | some v =>
            -- the view's own text, not the statement's: its errors point nowhere in it
            let (cq, ns, affs, colls, _) ← try compileSub { env with scopes := [] } v.q false fuel catch e => throw { e with pos := none }
            if !v.cols.isEmpty && v.cols.length != ns.size then throwC s!"expected {v.cols.length} columns for '{v.name}' but got {ns.size}"
            let ns := if v.cols.isEmpty then ns else v.cols.toArray
            pure (CSource.sub cq ns.size slot left right #[] #[],
              { name := an, cols := ns, affs, colls := colls.map fun c => (c.map (·.1)).getD .binary, base := slot,
                rowid := none : SrcInfo })
          | none =>
          let tbl := if nameEq name "sqlite_schema" || nameEq name "sqlite_master" then some schemaTable
            else if nameEq name "sqlite_temp_schema" || nameEq name "sqlite_temp_master" then
              some { schemaTable with name := "sqlite_temp_schema", root := tempRoot }
            else env.schema.table? qname
          match tbl with
          | none => throwC s!"no such table: {name}"
          | some t =>
            let n := t.cols.size
            pure (CSource.table t.root n t.ipk t.reals t.defaults slot .full left right t.layout #[],
              { name := an, cols := t.names, affs := t.affs, colls := t.colls, base := slot,
                rowid := if t.withoutRowid then none else some (slot + n), width := n + 1 : SrcInfo })
        | .call fname args alias =>
          let n := lowerAscii fname
          if n.startsWith "pragma_" then
            -- a schema pragma's rows, read for each row of the earlier items (the argument may name their columns)
            match schemaPragma env.schema (n.drop 7).toString "" with
            | none => throwC s!"no such table-valued function: {fname}"
            | some (ns, _) =>
              let env' := { env with scopes := { srcs := infos } :: env.scopes }
              let cargs ← compileList env' args fuel
              pure (CSource.tvf n (cargs.map (·.1)) ns.size slot left right #[],
                { name := alias.getD fname, cols := ns, affs := ns.map fun _ => .none, colls := ns.map fun _ => .binary,
                  base := slot, rowid := none : SrcInfo })
          else if n == "json_each" || n == "json_tree" then
            -- read per row of the earlier items: the arguments may name their columns
            let env' := { env with scopes := { srcs := infos } :: env.scopes }
            let cargs ← compileList env' args fuel
            if cargs.isEmpty || cargs.size > 2 then throwC s!"wrong number of arguments to function {fname}()"
            let ns := #["key", "value", "type", "atom", "id", "parent", "fullkey", "path"]
            pure (CSource.tvf n (cargs.map (·.1)) ns.size slot left right #[],
              { name := alias.getD fname, cols := ns, affs := ns.map fun _ => .none, colls := ns.map fun _ => .binary,
                base := slot, rowid := none, jsonEach := true : SrcInfo })
          else throwC s!"no such table-valued function: {fname}"
        | .subquery q alias =>
          let (cq, ns, affs, colls, _) ← compileSub env q true fuel
          pure (CSource.sub cq ns.size slot left right #[] #[],
            { name := alias.getD "", cols := ns, affs, colls := colls.map fun c => (c.map (·.1)).getD .binary, base := slot,
              rowid := none : SrcInfo })
termination_by structural fuel => fuel

/-- The FROM items: sources (from slot `slot0`, numbered from `j0`), their scope entries, the ON conditions (with the
source each belongs to), the slot after them, and what the items read in place hand the core. `shape`: the core as
select.c flattenSubquery reads it; `after`: the join after these items (inside an item read in place). -/
def compileFrom (env : CEnv) (shape : Shape) (slot0 j0 : Nat) (after : Option JoinKind) (arms : List Arm) : Array FromIn → Nat →
    CM (Array CSource × Array SrcInfo × Array (Nat × CExpr) × Nat × FlatOut)
  | _, 0 => throwC "query nested too deeply"
  | items, fuel+1 => do
    let mut srcs : Array CSource := #[]
    let mut infos : Array SrcInfo := #[]
    let mut ons : Array (Nat × CExpr) := #[]
    let mut slot := slot0
    let mut fo : FlatOut := { shape }
    let mut arms := arms
    for ((kind, item, on, usingCols), idx) in items.zipIdx do
      let left := kind == .left || kind == .full
      let right := kind == .right || kind == .full
      let j := j0 + srcs.size
      let next := (items[idx + 1]?.map (·.1)) <|> after
      -- read in place (select.c flattenSubquery): whole, or one arm of a UNION ALL; else a source
      let fsrc := flatSrc env item
      let mut plan : Option (Nat × Option (Array String × Array Aff × Array (Option (Collation × Bool))) × Bool) := none
      if let some fs := fsrc then
        let inView (e : CErr) : CErr := if fs.view.isSome then { e with pos := none } else e
        match ← (try flatPlan fs fo.shape j kind next fuel catch e => throw (inView e)) with
        | .no => pure ()
        | .simple drop => plan := some (0, none, drop)
        | .compound n ns as cs => match arms with
          | (k, ns', as', cs') :: more =>
            arms := more
            plan := some (k, some (ns', as', cs'), false)
          | [] => return (srcs, infos, ons, slot, { fo with fork := some (n, ns, as, cs) })
      let mut info : SrcInfo := default
      let mut src : Option CSource := none
      match plan, fsrc with
      | some (k, comp, drop), some fs =>
        if let some id := fs.cte then modify fun st => { st with cteReads := bumpRead st.cteReads id }
        let (isrcs, ions, islot, inf, x) ← try compileFlat fs k comp left drop fo.shape slot j next arms fuel
          catch e => throw (if fs.view.isSome then { e with pos := none } else e)
        if x.fork.isSome then return (srcs, infos, ons, slot, { fo with fork := x.fork })
        arms := x.arms
        srcs := srcs ++ isrcs
        ons := ons ++ ions
        slot := islot
        info := inf
        fo := { fo with
          shape := x.shape, conds := x.conds ++ fo.conds
          order := fo.order <|> x.order, limit := fo.limit <|> x.limit, ctes := fo.ctes ++ x.ctes }
      | _, _ =>
        let (s, inf) ← compileItem env infos item slot left right fuel
        src := some s
        info := inf
      -- USING: an equality with the column of an earlier item; the later column is merged away
      -- NATURAL: the columns this item shares with the earlier ones
      let usingCols := if usingCols == ["*"] then
          info.cols.toList.filter fun c => infos.any fun s => s.cols.toList.zipIdx.any fun (n, i) => nameEq n c && !(s.hidden.getD i false)
        else usingCols
      for u in usingCols do
        let some ri := info.cols.findIdx? (nameEq · u) | throwC s!"cannot join using column {u} - column not present in both tables"
        let some (lc, l) := (infos.toList.zipIdx.findSome? fun (s, _) =>
            (s.cols.findIdx? (nameEq · u)).bind fun ci => if s.hidden.getD ci false then none else some (ci, s))
          | throwC s!"cannot join using column {u} - column not present in both tables"
        let le ← if l.flat.isEmpty then pure (CExpr.col 0 (l.base + lc)) else compileFlatCol env (.ref l lc) 0 env.scopes fuel
        let re ← if info.flat.isEmpty then pure (CExpr.col 0 (info.base + ri)) else compileFlatCol env (.ref info ri) 0 env.scopes fuel
        ons := ons.push (j, .cmp .eq le re (cmpAff (l.affs.getD 0 .none) .none) (l.colls.getD 0 .binary))
        let hidden := if info.hidden.size < info.cols.size then Array.replicate info.cols.size false else info.hidden
        info := { info with hidden := hidden.setIfInBounds ri true }
      infos := infos.push info
      if let some s := src then
        srcs := srcs.push s
        slot := slot + info.slots
      -- ON sees this item and the earlier ones
      if let some o := on then
        let env' := { env with scopes := { srcs := infos } :: env.scopes }
        -- (sqlite3 gives an error in an ON clause no offset)
        let cs ← try compileList env' (conjuncts o 64) fuel catch e => throw { e with pos := none }
        ons := ons ++ cs.map fun (c, _, _) => (j, c)
    return (srcs, infos, ons, slot, { fo with arms })
termination_by structural _ fuel => fuel

/-- Whether FROM item `j` (joined by `kind`, followed by `next`) of a core shaped `shape` reads `fs` in place: select.c
flattenSubquery's conditions (numbered as there) and its caller's in sqlite3Select. -/
def flatPlan (fs : FlatSrc) (shape : Shape) (j : Nat) (kind : JoinKind) (next : Option JoinKind) : Nat → CM FlatPlan
  | 0 => pure .no
  | fuel+1 => do
    let .mk rec ctes first rest orderBy limit offset := fs.q
    let arms := first :: rest.map (·.2)
    -- (7), (17c): each arm has a FROM clause
    let some facts := arms.mapM (coreFacts orderBy) | return .no
    let some f0 := facts.head? | return .no
    let lim := limit.isSome
    let outerJ := kind == .left || kind == .right || kind == .full
    -- tag-select-0230: an ORDER BY that changes nothing is dropped first
    let drop := !orderBy.isEmpty && (shape.hasOrder || shape.nsrc > 1) && !lim && !shape.orderReqd
    let order := !orderBy.isEmpty && !drop
    let isOuterKind (k : JoinKind) : Bool := k == .left || k == .right || k == .full
    if offset.isSome                                                     -- (14)
      || shape.win || facts.any (·.win)                                  -- (25)
      || facts.any (·.agg)                                               -- an aggregate subquery
      || lim && (shape.hasLimit || shape.compound || shape.nsrc > 1 || shape.agg || shape.hasWhere || shape.distinct)
                                                                         -- (13) (15) (8) (9) (19) (21)
      || f0.distinct                                                     -- (4)
      || order && (shape.hasOrder || shape.agg || shape.compound)        -- (11) (16); an arm sorts nothing
      || order && j == 0 && shape.complex && (shape.nsrc == 1 || next.any isOuterKind)  -- a complex result
      || facts.any (·.right) && j > 0                                    -- (27a)
      || shape.hasRight                                                  -- (one RIGHT JOIN per SELECT here)
      || outerJ && (kind != .left || f0.nitems > 1 || shape.distinct || !rest.isEmpty || order
                    || !rowidTable fs.env ctes f0.only)                  -- (26) (3a) (3d) (17f)
      || !ctes.isEmpty && shape.noCompound then                          -- (a recursive SELECT has no WITH tables)
      return .no
    if rest.isEmpty then return .simple drop
    -- (17a) (17b) (17d) (18) (20) (23); a UNION ALL with a LIMIT stays a subquery
    if order || shape.agg || shape.distinct || facts.any (·.distinct) || !rest.all (·.1 == .unionAll)
      || shape.hasOrder && !shape.orderCols || shape.noCompound || shape.handed || lim then
      return .no
    -- (17h): each arm's columns have the first arm's affinities
    let st0 ← get
    let (env2, _) ← compileCtes fs.env rec ctes fuel
    let mut res := #[]
    for a in arms do
      let (_, ns, affs, colls, _) ← compileCore env2 a none true false false fuel
      res := res.push (ns, affs, colls)
    set st0
    let some (ns, affs0, colls) := res[0]? | return .no
    if res.any (fun (_, a, _) => a != affs0) then return .no
    return .compound arms.length ns affs0 colls
termination_by structural fuel => fuel

/-- A FROM item read in place (select.c flattenSubquery): arm `k` of `fs.q` (read under the compound's names,
affinities and collations `comp`, for an arm of a UNION ALL) compiled into the reading core's frame from slot `slot`, its
sources numbered from `j`; `next`: the join after it. `left`: it is a LEFT JOIN's right side; `drop`: its ORDER BY is
dropped (tag-select-0230). Its own FROM items are tried in place in turn, `shape` being the reading core with this
item merged. Returns its sources, their ON conditions, the slot after them, the scope entry that stands for it, and
what it hands the reading core. -/
def compileFlat (fs : FlatSrc) (k : Nat) (comp : Option (Array String × Array Aff × Array (Option (Collation × Bool))))
    (left drop : Bool) (shape : Shape) (slot j : Nat) (next : Option JoinKind) (arms : List Arm) :
    Nat → CM (Array CSource × Array (Nat × CExpr) × Nat × SrcInfo × FlatOut)
  | 0 => throwC "query nested too deeply"
  | fuel+1 => do
    let .mk rec ctes first rest orderBy limit _ := fs.q
    let core := if k == 0 then first else ((rest.drop (k - 1)).head?.map (·.2)).getD first
    let .select _ cols fromItem joins whereE _ _ := core | throwC "lean-sqlite: a VALUES read in place"
    let order := !orderBy.isEmpty && !drop && comp.isNone
    let items : Array FromIn := ((match fromItem with | some f => [(JoinKind.inner, f, none, [])] | none => [])
      ++ joins.map fun (.mk kd it on u) => (kd, it, on, u)).toArray
    let shape := { shape with
      nsrc := shape.nsrc + items.size - 1
      hasWhere := shape.hasWhere || whereE.isSome || joins.any fun (.mk _ _ on u) => on.isSome || !u.isEmpty
      hasOrder := shape.hasOrder || order
      hasLimit := shape.hasLimit || limit.isSome
      compound := shape.compound || comp.isSome
      hasRight := shape.hasRight || joins.any fun (Join.mk kd _ _ _) => kd == JoinKind.right || kd == JoinKind.full
      handed := shape.handed || order || limit.isSome }
    let (envQ, cctes) ← compileCtes fs.env rec ctes fuel
    let (isrcs, iinfos, ions, islot, x) ← compileFrom envQ shape slot j next arms items fuel
    if x.fork.isSome then return (#[], #[], slot, default, x)
    let isrcs := if left then isrcs.modify 0 CSource.setLeft else isrcs
    let env' := { envQ with scopes := { srcs := iinfos } :: envQ.scopes }
    -- result columns: compiled here once (errors, types, names), and again wherever the reading core names them
    let mut flat : Array FlatCol := #[]
    let mut ccols : Array CExpr := #[]
    let mut names : Array String := #[]
    let mut affs : Array Aff := #[]
    let mut colls : Array (Option (Collation × Bool)) := #[]
    for rc in cols do
      match rc with
      | .star =>
        if iinfos.isEmpty then throwC "no tables specified"
        for s in iinfos do
          for i in [0:s.cols.size] do
            unless s.hidden.getD i false do
              let r : FlatCol := if s.flat.isEmpty then .slot (s.base + i) else .ref s i
              flat := flat.push r
              ccols := ccols.push (← compileFlatCol envQ r 0 envQ.scopes fuel)
              names := names.push (s.cols.getD i "")
              affs := affs.push (s.affs.getD i .none); colls := colls.push (some (s.colls.getD i .binary, false))
      | .tableStar t =>
        match iinfos.find? (nameEq ·.name t) with
        | none => throwC s!"no such table: {t}"
        | some s =>
          for i in [0:s.cols.size] do
            let r : FlatCol := if s.flat.isEmpty then .slot (s.base + i) else .ref s i
            flat := flat.push r
            ccols := ccols.push (← compileFlatCol envQ r 0 envQ.scopes fuel)
            names := names.push (s.cols.getD i "")
            affs := affs.push (s.affs.getD i .none); colls := colls.push (some (s.colls.getD i .binary, false))
      | .expr e alias span =>
        let (ce, a, kk) ← compileExpr env' e fuel
        flat := flat.push (.expr e); ccols := ccols.push ce; affs := affs.push a; colls := colls.push kk
        names := names.push (match alias with
          | some n => n
          | none => match e with
            | .col tbl n _ _ => colName iinfos tbl n
            | _ => span)
    if let (some v, some ns) := (fs.view, fs.names) then
      if ns.size != names.size then throwC s!"expected {ns.size} columns for '{v}' but got {names.size}"
    if let some (ns, as, cs) := comp then
      names := ns; affs := as; colls := cs
    if let some ns := fs.names then names := ns
    -- WHERE: ahead of the reading core's own (flattenSubquery puts pSub->pWhere first); a LEFT JOIN's ON terms
    let aliasList := cols.filterMap fun | .expr e (some a) _ => some (a, e) | _ => none
    let envA := { env' with aliases := aliasList }
    let wconds ← compileList envA (match whereE with | some w => conjuncts w 64 | none => []) fuel
    -- ORDER BY and LIMIT, handed to the reading SELECT
    let ord ← if !order then pure none else do
      let mut out := #[]
      let mut i := 0
      for .mk e _ _ in orderBy do
        i := i + 1
        let e0 := stripCollate e
        match e0 with
        | .lit (.int n) =>
          if n < 1 || n.toNatClampNeg > ccols.size then
            throwC s!"{ordinalName i} ORDER BY term out of range - should be between 1 and {ccols.size}"
          out := out.push (ccols.getD (n.toNatClampNeg - 1) default)
        | .col none n _ _ =>
          match cols.findIdx? (fun | .expr _ (some a) _ => nameEq a n | _ => false) with
          | some jj => out := out.push (ccols.getD jj default)
          | none => let (c, _, _) ← compileExpr envA e0 fuel; out := out.push c
        | _ => let (c, _, _) ← compileExpr envA e0 fuel; out := out.push c
      let dirs := orderBy.toArray.map fun (t : OrderTerm) =>
        let d := dirOf t names colls
        match t with
        | .mk e _ _ => if (orderTermColl e).isSome then d else match exprColl envQ core e with
          | some c => (d.1, d.2.1, c)
          | none => d
      pure (some (out, dirs))
    let lim ← match limit with
      | some e => do let r ← compileExpr envQ e fuel; pure (some r.1)
      | none => pure none
    let nullRow := if !left then none else match isrcs[0]? with
      | some (CSource.table _ n _ _ _ base _ _ _ layout _) => if layout.isEmpty then some (base + n) else none
      | _ => none
    let info : SrcInfo := {
      name := fs.alias, cols := names, affs, colls := colls.map fun c => (c.map (·.1)).getD .binary,
      base := slot, rowid := none, flat, inner := iinfos, flatCtes := envQ.ctes,
      flatPad := fs.pad, flatNull := nullRow }
    let hoisted := (cctes.zip ctes.toArray).map fun (c, Cte.mk _ _ _ m) => (c, m)
    return (isrcs, ions, islot, info, { x with
      conds := x.conds ++ wconds.map (fun (t : Typed) => (j, t.1)), order := ord <|> x.order, limit := lim <|> x.limit
      ctes := hoisted ++ x.ctes })
termination_by structural fuel => fuel

/-- Column `r` of a FROM item read in place, named `d` levels in from the core that reads the item (`parents`: the
scopes enclosing that core): its expression compiled there (select.c substExpr), so a column never named is never
computed; on a LEFT JOIN's missing row NULL, unless it is a column of the item. -/
def compileFlatCol (env : CEnv) (r : FlatCol) (d : Nat) (parents : List Scope) : Nat → CM CExpr
  | 0 => throwC "expression nested too deeply"
  | fuel+1 => match r with
    | .slot s => do
      modify fun st => { st with outer := max st.outer d }
      pure (.col d s)
    | .expr _ => pure (.lit .null)
    | .ref si i => do
      let outer := List.replicate si.flatPad {} ++ parents.drop si.flatPad
      let e ← match si.flat[i]? with
        | some (.expr x) => do
          let reads := (← get).cteReads
          let envX := { env with
            scopes := List.replicate d {} ++ ({ srcs := si.inner } :: outer), ctes := si.flatCtes, aliases := [] }
          let (ce, _, _) ← compileExpr envX x fuel
          -- (its WITH tables were counted where it was compiled first)
          modify fun st => { st with cteReads := reads }
          pure ce
        | some c => compileFlatCol env c d outer fuel
        | none => pure (.lit .null)
      let missing (row : Nat) : CExpr := .case none #[(.isNull (.col d row) false, .lit .null)] (some e) .none .binary
      match si.flatNull, e with
      | some row, .col d' _ => pure (if d' == d then e else missing row)
      | some row, _ => pure (missing row)
      | none, _ => pure e
termination_by structural fuel => fuel
end

end LSql

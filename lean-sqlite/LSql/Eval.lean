import LSql.Compile
import LSql.BTree
import LSql.DateTime
import LSql.Json
/-! Running compiled SELECTs (sqlite's VDBE role, as a tree-walking interpreter over immutable state): expression
evaluation, the nested-loop join, aggregation, compound operators, ORDER BY and LIMIT. -/
namespace LSql

abbrev Row := Array Value
abbrev EM := Except String

structure Env where
  pager : Pager
  /-- the row frames of the enclosing queries, the current one last -/
  frames : Array Row := #[]
  ctes : Array (Array Row) := #[]
  aggs : Array Value := #[]
  /-- the current row's window function values -/
  wins : Array Value := #[]
  /-- the statement's time ('now'), Unix milliseconds -/
  nowMs : Option Int64 := none
  /-- the schema (for the pragma_* table-valued functions) -/
  schema : Schema := {}
  /-- which aggregate values carry sqlite's JSON subtype (json_group_array/object results) -/
  aggJson : Array Bool := #[]
  lastRowid : Int64 := 0
  changes : Int64 := 0
  totalChanges : Int64 := 0
  deriving Inhabited

namespace Env
@[inline] def col (env : Env) (d s : Nat) : Value :=
  if d < env.frames.size then (env.frames.getD (env.frames.size - 1 - d) #[]).getD s .null else .null
@[inline] def push (env : Env) (r : Row) : Env := { env with frames := env.frames.push r }
end Env

@[inline] def boolV (b : Bool) : Value := .int (if b then 1 else 0)
@[inline] def isTrueV (v : Value) : Bool := v.truth? == some true

def optBool : Option Bool → Value
  | none => .null
  | some b => boolV b

/-- The error a RAISE() makes: a marker the statement layer reads (IGNORE skips the row; the others fail with the
message). -/
def raiseMsg (k : RaiseKind) (m : String) : String :=
  "\x01RAISE:" ++ (match k with | .ignore => "IGNORE" | .rollback => "ROLLBACK" | .abort => "ABORT" | .fail => "FAIL") ++ ":" ++ m

instance : BEq Value where
  beq a b := match a, b with
    | .null, .null => true
    | .int x, .int y => x == y
    | .real x, .real y => x == y
    | .text x, .text y => x == y
    | .blob x, .blob y => x == y
    | _, _ => false

/-- A comparison after applying the comparison affinity to both sides (NULL unless IS / IS NOT). -/
def compareV (op : BinOp) (aff : Aff) (coll : Collation) (a b : Value) : Value :=
  let a := Value.applyAff aff a
  let b := Value.applyAff aff b
  match op with
  | .is => boolV (isSame a b)
  | .isNot => boolV (!isSame a b)
  | _ =>
    if a.isNull || b.isNull then .null else
    let o := cmpValues coll a b
    boolV (match op with
      | .eq => o == .eq | .ne => o != .eq | .lt => o == .lt | .le => o != .gt | .gt => o == .gt | .ge => o != .lt
      | _ => false)
where
  isSame (a b : Value) : Bool := match a, b with
    | .null, .null => true
    | .null, _ | _, .null => false
    | _, _ => cmpValues coll a b == .eq

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

/-- A value as a rowid, if it equals one. -/
def toRowid? (v : Value) : Option Int64 :=
  match Value.applyAff .integer v with
  | .int i => some i
  | _ => none

def textArg (v : Value) : String := v.toText

/-- soundex() (func.c soundexFunc): the first letter, then up to three digit codes; "?000" without a letter. -/
def soundex (v : Value) : String :=
  let code (c : Char) : Nat :=
    let u := c.toUpper
    if "BFPV".contains u then 1 else if "CGJKQSXZ".contains u then 2 else if "DT".contains u then 3
    else if u == 'L' then 4 else if "MN".contains u then 5 else if u == 'R' then 6 else 0
  let cs := (match v with | .null => "" | v => v.toText).toList.dropWhile (fun (c : Char) => !(c.isAlpha && c.toNat < 128))
  match cs with
  | [] => "?000"
  | c :: rest =>
    let (ds, _) := rest.foldl (fun (acc : List Nat × Nat) (ch : Char) =>
      let (ds, prev) := acc
      if ds.length ≥ 3 || !(ch.toNat < 128) then acc else
      let k := code ch
      if k > 0 && k != prev then (ds ++ [k], k) else (ds, if ch.isAlpha then k else prev)) ([], code c)
    let s := String.singleton c.toUpper ++ String.join (ds.map toString)
    s.pushn '0' (4 - s.length)

/-- splitmix64: a well-mixed 64-bit step. -/
def splitmix (x : UInt64) : UInt64 :=
  let z := x + 0x9E3779B97F4A7C15
  let z := (z ^^^ (z >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  z ^^^ (z >>> 31)

/-- A seed from the statement's time, a call site, and the current row's values. -/
def seedOf (env : Env) (site : Int64) : UInt64 :=
  let row := env.frames.back?.getD #[]
  let h := row.foldl (fun (h : UInt64) v => splitmix (h ^^^ hash v.toText ^^^ (v.typeName.length.toUInt64 <<< (56 : UInt64)))) 0
  splitmix ((env.nowMs.getD 0).toUInt64 ^^^ splitmix site.toUInt64 ^^^ h)

/-- The scalar functions (func.c). -/
def evalFn (env : Env) (name : String) (a : Array Value) : EM Value :=
  if name == jsonValueTag then .ok (a.getD 0 .null) else
  if DateTime.isDateFn name then DateTime.call name a env.nowMs else
  let x := a.getD 0 .null
  let y := a.getD 1 .null
  let z := a.getD 2 .null
  let anyNull := a.any (·.isNull)
  match name with
  | "ABS" => absV x
  | "LENGTH" => .ok (match x with
    | .null => .null
    | .blob b => .int b.size.toInt64
    | v => .int (v.toText.takeWhile (· != '\x00')).length.toInt64)
  | "OCTET_LENGTH" => .ok (match x with | .null => .null | v => .int v.toBytes.size.toInt64)
  | "LOWER" => .ok (match x with | .null => .null | v => .text (lowerAscii v.toText))
  | "UPPER" => .ok (match x with | .null => .null | v => .text (upperAscii v.toText))
  | "TYPEOF" => .ok (.text x.typeName)
  | "HEX" => .ok (.text (hexOf x.toBytes))
  | "QUOTE" => .ok (.text (quoteV x))
  | "UNICODE" => .ok (unicodeV x)
  | "CHAR" => .ok (charV a)
  | "COALESCE" => .ok ((a.find? (!·.isNull)).getD .null)
  | "IFNULL" => .ok (if x.isNull then y else x)
  | "NULLIF" => .ok (if !x.isNull && !y.isNull && cmpValues .binary x y == .eq then .null else x)
  | "IIF" | "IF" => .ok (if x.truth? == some true then y else z)
  | "INSTR" => .ok (instrV x y)
  | "SUBSTR" | "SUBSTRING" =>
    .ok (if x.isNull || y.isNull || (a.size > 2 && z.isNull) then .null
      else substrV x (Num.castToInt y) (if a.size > 2 then some (Num.castToInt z) else none))
  | "REPLACE" =>
    .ok (if anyNull then .null else
      let s := x.toText
      let f := y.toText
      if f.isEmpty then .text s else .text (s.replace f z.toText))
  | "TRIM" | "LTRIM" | "RTRIM" =>
    .ok (if x.isNull || (a.size > 1 && y.isNull) then .null else
      let cs := if a.size > 1 then y.toText.toList else [' ']
      .text (trimChars x.toText cs (name != "RTRIM") (name != "LTRIM")))
  | "ROUND" => .ok (roundV x a[1]?)
  | "MIN" | "MAX" =>
    .ok (if anyNull then .null else
      a.foldl (fun (best : Value) v =>
        let o := cmpValues .binary v best
        if (name == "MIN" && o == .lt) || (name == "MAX" && o == .gt) then v else best) x)
  | "LIKE" =>
    if x.isNull || y.isNull || (a.size > 2 && z.isNull) then .ok .null else
    let esc := if a.size > 2 then (z.toBytes)[0]? else none
    .ok (boolV (likeMatch x.toBytes y.toBytes esc))
  | "GLOB" => .ok (if anyNull then .null else boolV (globMatch x.toBytes y.toBytes))
  | "PRINTF" | "FORMAT" => .ok (if x.isNull then .null else .text (Num.printf x.toText (a.toList.drop 1)))
  | "CONCAT" => .ok (.text (a.foldl (fun s v => if v.isNull then s else s ++ v.toText) ""))
  | "CONCAT_WS" =>
    .ok (if x.isNull then .null else
      let parts := (a.toList.drop 1).filter (!·.isNull) |>.map (·.toText)
      .text (x.toText.intercalate parts))
  | "LAST_INSERT_ROWID" => .ok (.int env.lastRowid)
  | "CHANGES" => .ok (.int env.changes)
  | "TOTAL_CHANGES" => .ok (.int env.totalChanges)
  | "SQLITE_VERSION" => .ok (.text "3.54.0")
  | "SQLITE_SOURCE_ID" => .ok (.text "lean-sqlite")
  | "SIGN" => .ok (signV x)
  | "SQRT" => .ok (math1 (fun f => if f < 0 then 0.0/0.0 else f.sqrt) x)
  | "EXP" => .ok (math1 Float.exp x)
  | "LN" => .ok (math1 (fun f => if f ≤ 0 then 0.0/0.0 else f.log) x)
  | "LOG10" => .ok (math1 (fun f => if f ≤ 0 then 0.0/0.0 else f.log10) x)
  | "LOG2" => .ok (math1 (fun f => if f ≤ 0 then 0.0/0.0 else f.log2) x)
  | "LOG" =>
    if a.size == 1 then .ok (math1 (fun f => if f ≤ 0 then 0.0/0.0 else f.log10) x) else
    match numOf x, numOf y with
    | .null, _ | _, .null => .ok .null
    | b, v => let b := toF b; let v := toF v
      .ok (if b ≤ 0 || b == 1 || v ≤ 0 then .null else realV (v.log / b.log))
  | "CEIL" | "CEILING" => .ok (intRound Float.ceil x)
  | "FLOOR" => .ok (intRound Float.floor x)
  | "TRUNC" => .ok (intRound (fun f => if f ≥ 0 then f.floor else f.ceil) x)
  | "SIN" => .ok (math1 Float.sin x) | "COS" => .ok (math1 Float.cos x) | "TAN" => .ok (math1 Float.tan x)
  | "ASIN" => .ok (math1 Float.asin x) | "ACOS" => .ok (math1 Float.acos x) | "ATAN" => .ok (math1 Float.atan x)
  | "SINH" => .ok (math1 Float.sinh x) | "COSH" => .ok (math1 Float.cosh x) | "TANH" => .ok (math1 Float.tanh x)
  | "ASINH" => .ok (math1 Float.asinh x) | "ACOSH" => .ok (math1 Float.acosh x) | "ATANH" => .ok (math1 Float.atanh x)
  | "DEGREES" => .ok (math1 (fun f => f * 180.0 / 3.141592653589793) x)
  | "RADIANS" => .ok (math1 (fun f => f * 3.141592653589793 / 180.0) x)
  | "PI" => .ok (.real 3.141592653589793)
  | "POW" | "POWER" =>
    .ok (match numOf x, numOf y with | .null, _ | _, .null => .null | b, e => realV (Float.pow (toF b) (toF e)))
  | "ATAN2" =>
    .ok (match numOf x, numOf y with | .null, _ | _, .null => .null | b, e => realV (Float.atan2 (toF b) (toF e)))
  | "MOD" =>
    .ok (match numOf x, numOf y with
      | .null, _ | _, .null => .null
      | b, e => let d := toF e; if d == 0 then .null else
        let q := toF b / d
        let t := if q ≥ 0 then q.floor else q.ceil
        realV (toF b - t * d))
  | "ZEROBLOB" => .ok (.blob (pushZeros ByteArray.empty (Num.castToInt x).toNatClampNeg))
  | "UNHEX" => .ok (unhexV x)
  | "LIKELY" | "UNLIKELY" | "LIKELIHOOD" => .ok x
  | "SOUNDEX" => .ok (.text (soundex x))
  | "RANDOM" =>
    -- a pseudo-random number: the statement's clock, the call site (its last argument) and the current row, mixed
    .ok (.int (splitmix (seedOf env (Num.castToInt (a.getD 0 .null)))).toInt64)
  | "RANDOMBLOB" =>
    let n := max 1 (Num.castToInt x).toNatClampNeg
    let s0 := seedOf env (Num.castToInt (a.getD 1 .null))
    let (b, _) := n.fold (fun _ _ (acc : ByteArray × UInt64) =>
      let s := splitmix acc.2
      (acc.1.push s.toUInt8, s)) (ByteArray.empty, s0)
    .ok (.blob b)
  | _ => .error s!"no such function: {name}"

/-! ## Aggregates (func.c sumStep, countStep, minmaxStep, groupConcatStep) -/

structure AggAcc where
  n : Int64 := 0
  isum : Int64 := 0
  rsum : Float := 0
  rerr : Float := 0
  approx : Bool := false
  ovrfl : Bool := false
  best : Value := .null
  bestAt : Nat := 0
  str : String := ""
  any : Bool := false
  /-- DISTINCT: the argument lists seen, replayed when the group ends (and, for a JSON aggregate, which are JSON) -/
  seen : Array (Array Value) := #[]
  seenJ : Array (Array Bool) := #[]
  /-- json_group_array / json_group_object -/
  json : Json.Agg := {}
  /-- the percentile family: the inputs, the fraction (fixed by the first row), the first error -/
  ys : Array Float := #[]
  pct : Option Float := none
  err : Option String := none
  deriving Inhabited

/-- median, percentile, percentile_cont, percentile_disc -/
def isPercentile (name : String) : Bool :=
  name == "MEDIAN" || name == "PERCENTILE" || name == "PERCENTILE_CONT" || name == "PERCENTILE_DISC"

/-- One row of a percentile aggregate (sqlite's percentStep): checks the fraction, skips NULL, keeps numbers. -/
def percentStep (name : String) (acc : AggAcc) (args : Array Value) : AggAcc :=
  if acc.err.isSome then acc else
  let fname := name.toLower
  let fail (m : String) : AggAcc := { acc with err := some m }
  let mxFrac : Float := if name == "PERCENTILE" then 100.0 else 1.0
  let pctE : Except String Float :=
    if name == "MEDIAN" then .ok 0.5 else
    let p := Value.applyAff .numeric (args.getD 1 .null)
    let r := (Num.castToReal p) / mxFrac
    let isNum := match p with | .int _ | .real _ => true | _ => false
    if !isNum || r < 0.0 || r > 1.0 then
      .error s!"the fraction argument to {fname}() is not between 0.0 and {if name == "PERCENTILE" then "100.0" else "1.0"}"
    else .ok r
  match pctE with
  | .error m => fail m
  | .ok r =>
    match acc.pct with
    | some r0 => if (r0 - r) < -0.001 || (r0 - r) > 0.001 then
        fail s!"the fraction argument to {fname}() is not the same for all input rows" else step r
    | none => step r
where
  step (r : Float) : AggAcc :=
    let acc := { acc with pct := some r }
    match args.getD 0 .null with
    | .null => acc
    | .int i => { acc with ys := acc.ys.push i.toFloat }
    | .real y => if y.isInf || y.isNaN then { acc with err := some s!"Inf input to {name.toLower}()" }
      else { acc with ys := acc.ys.push y }
    | _ => { acc with err := some s!"input to {name.toLower}() is not numeric" }

/-- A percentile aggregate's result (sqlite's percentCompute): NULL for no rows; percentile_disc takes the element at
the fraction, the others interpolate between its neighbours. -/
def percentFinal (name : String) (acc : AggAcc) : EM Value :=
  match acc.err with
  | some m => .error m
  | none =>
    if acc.ys.isEmpty then .ok .null else
    let a := (acc.ys.toList.mergeSort fun x y => x <= y).toArray
    let n := a.size
    let ix := acc.pct.getD 0.5 * (n - 1).toFloat
    let i1 := ix.toUInt64.toNat
    let v1 := a.getD i1 0.0
    if name == "PERCENTILE_DISC" then .ok (.real v1) else
    let i2 := if ix == i1.toFloat || i1 == n - 1 then i1 else i1 + 1
    let v2 := a.getD i2 0.0
    .ok (.real (v1 + (v2 - v1) * (ix - i1.toFloat)))

/-- kahanBabuskaNeumaierStep -/
def kbn (acc : AggAcc) (r : Float) : AggAcc :=
  let s := acc.rsum
  let t := s + r
  let err := if s.abs > r.abs then (s - t) + r else (r - t) + s
  { acc with rsum := t, rerr := acc.rerr + err }

def kbnInt (acc : AggAcc) (i : Int64) : AggAcc :=
  if i ≤ -4503599627370496 || i ≥ 4503599627370496 then
    let sm := i % 16384
    kbn (kbn acc (i - sm).toFloat) sm.toFloat
  else kbn acc i.toFloat

def kbnInit (acc : AggAcc) (i : Int64) : AggAcc :=
  if i ≤ -4503599627370496 || i ≥ 4503599627370496 then
    let sm := i % 16384
    { acc with rsum := (i - sm).toFloat, rerr := sm.toFloat }
  else { acc with rsum := i.toFloat, rerr := 0 }

def aggStep (name : String) (star : Bool) (coll : Collation) (acc : AggAcc) (args : Array Value) (at_ : Nat) : AggAcc :=
  let x := args.getD 0 .null
  if Json.isJsonAgg name then { acc with json := Json.aggStep name acc.json args (args.map fun _ => false) } else
  if isPercentile name then percentStep name acc args else
  match name with
  | "COUNT" => if star || !x.isNull then { acc with n := acc.n + 1 } else acc
  | "SUM" | "TOTAL" | "AVG" =>
    if x.isNull then acc else
    let acc := { acc with n := acc.n + 1 }
    let nt := match x with | .text _ | .blob _ => Value.applyAff .numeric x | v => v
    match nt with
    | .int i =>
      if !acc.approx then
        match Num.addInt? acc.isum i with
        | some s => { acc with isum := s }
        | none => kbnInt { (kbnInit acc acc.isum) with approx := true, ovrfl := true } i
      else kbnInt acc i
    | v =>
      let r := Num.castToReal v
      if !acc.approx then kbn { (kbnInit acc acc.isum) with approx := true } r
      else kbn { acc with ovrfl := false } r
  | "MIN" | "MAX" =>
    if x.isNull then acc else
    if !acc.any then { acc with best := x, bestAt := at_, any := true } else
    let o := cmpValues coll x acc.best
    if (name == "MIN" && o == .lt) || (name == "MAX" && o == .gt) then { acc with best := x, bestAt := at_ } else acc
  | _ => -- GROUP_CONCAT, STRING_AGG
    if x.isNull then acc else
    let sep := if args.size > 1 then (args.getD 1 .null).toText else ","
    if acc.any then { acc with str := acc.str ++ sep ++ x.toText } else { acc with str := x.toText, any := true }

def aggFinal (name : String) (acc : AggAcc) : EM Value :=
  if Json.isJsonAgg name then Json.aggFinal name acc.json else
  if isPercentile name then percentFinal name acc else
  let r := if acc.approx then (if acc.rerr.isInf || acc.rerr.isNaN then acc.rsum else acc.rsum + acc.rerr) else acc.isum.toFloat
  match name with
  | "COUNT" => .ok (.int acc.n)
  | "SUM" =>
    if acc.n == 0 then .ok .null
    else if acc.approx then (if acc.ovrfl then .error "integer overflow" else .ok (.real r))
    else .ok (.int acc.isum)
  | "AVG" => .ok (if acc.n == 0 then .null else .real (r / acc.n.toFloat))
  | "TOTAL" => .ok (.real r)
  | "MIN" | "MAX" => .ok acc.best
  | _ => .ok (if acc.any then .text acc.str else .null)

/-! ## Rows -/

/-- A table row's slot values: its columns (an INTEGER PRIMARY KEY is the rowid, a REAL column's integers are reals,
a column the record lacks has its default), then the rowid. -/
def decodeRow (n : Nat) (ipk : Option Nat) (realCols : Array Bool) (defaults : Array Value) (rowid : Int64)
    (rec : ByteArray) : Row :=
  let fs := recordFields rec
  let row := (List.range n).toArray.map fun i =>
    if ipk == some i then .int rowid else
    match fs[i]? with
    | some (t, o) =>
      let v := decodeField rec o t
      match v with
      | .int k => if realCols.getD i false then .real k.toFloat else v
      | v => v
    | none => defaults.getD i .null
  row.push (.int rowid)

/-- Writes a table row into a frame from slot `base`: the columns `need` marks (an INTEGER PRIMARY KEY is the rowid, a REAL
column's integers are reals, a column the record lacks has its default), then the rowid. -/
def fillRow (frame : Row) (base n : Nat) (ipk : Option Nat) (realCols : Array Bool) (defaults : Array Value)
    (need : Array Bool) (rowid : Int64) (rec_ : ByteArray) : Row :=
  let (hs, k) := getVarint rec_ 0
  let frame := go frame hs.toNat k hs.toNat 0 (n + 1)
  let frame := match ipk with | some i => frame.setIfInBounds (base + i) (.int rowid) | none => frame
  frame.setIfInBounds (base + n) (.int rowid)
where
  go (fr : Row) (hs pos body i : Nat) : Nat → Row
    | 0 => fr
    | f+1 =>
      if i ≥ n then fr else
      if pos ≥ hs then
        -- columns past the record's end (added by ALTER TABLE): their defaults
        go (if need.getD (base + i) true then fr.setIfInBounds (base + i) (defaults.getD i .null) else fr) hs pos body (i+1) f
      else
      let (t, l) := getVarint rec_ pos
      let fr := if need.getD (base + i) true then
          let v := decodeField rec_ body t
          let v := match v with | .int x => if realCols.getD i false then .real x.toFloat else v | v => v
          fr.setIfInBounds (base + i) v
        else fr
      go fr hs (pos + l) (body + serialLen t) (i+1) f

/-- A WITHOUT ROWID table's record as a row of slots: each field in its column (`layout`), the rowid slot NULL. -/
def worRow (n : Nat) (layout : Array Nat) (realCols : Array Bool) (rec_ : ByteArray) : Row :=
  let vs := decodeRecord rec_
  layout.size.fold (fun k _ (row : Row) =>
    let c := layout.getD k 0
    let v := vs.getD k .null
    let v := match v with | .int x => if realCols.getD c false then .real x.toFloat else v | v => v
    row.setIfInBounds c v) (Array.replicate (n + 1) .null)

/-- The frame with candidate `j` of a FROM item bound into its slots. -/
def bindCand (src : CSource) (need : Array Bool) (frame : Row) (raw : Array (Int64 × ByteArray)) (cands : Array Row)
    (j : Nat) : Row :=
  let (base, tbl) := match src with
    | .table _ tn ipk rc dv base _ _ _ _ _ => (base, some (tn, ipk, rc, dv))
    | .sub _ _ base _ _ _ | .cte _ _ base _ _ _ | .tvf _ _ _ base _ _ _ => (base, none)
  match tbl, raw.isEmpty with
  | some (tn, ipk, rc, dv), false =>
    let (k, r) := raw.getD j (0, ByteArray.empty)
    fillRow frame base tn ipk rc dv need k r
  | _, _ =>
    let c := cands.getD j #[]
    c.size.fold (fun k _ (fr : Row) => fr.setIfInBounds (base + k) (c.getD k .null)) frame

/-- json_each / json_tree rows (the JSON module's). -/
def tvfRows (tree : Bool) (json : Value) (root : Option Value) : EM (Array Row) :=
  Json.eachRows tree json root

def boundExprs : CBound → Array CExpr
  | .preceding e | .following e => #[e]
  | _ => #[]

/-- The slots a core reads (all, when a correlated subquery may read any). -/
def neededSlots (width : Nat) (exprs : Array CExpr) : Array Bool :=
  let (ss, corr) := exprs.foldl (fun (acc : Array Nat × Bool) e => let (s, c) := slotsOf e 64; (acc.1 ++ s, acc.2 || c)) (#[], false)
  if corr then Array.replicate width true else ss.foldl (fun m s => m.setIfInBounds s true) (Array.replicate width false)

/-- Orders rows by sort keys under ORDER BY directions. -/
def cmpKeys (dirs : Array (Bool × Bool × Collation)) (a b : Row) : Ordering :=
  go 0 dirs.size
where
  go (k : Nat) : Nat → Ordering
    | 0 => .eq
    | f+1 =>
      let (desc, nullsFirst, coll) := dirs.getD k (false, true, .binary)
      let x := a.getD k .null
      let y := b.getD k .null
      let o := match x, y with
        | .null, .null => .eq
        | .null, _ => if nullsFirst then .lt else .gt
        | _, .null => if nullsFirst then .gt else .lt
        | _, _ => let o := cmpValues coll x y; if desc then o.swap else o
      if o != .eq then o else go (k+1) f

/-- Compares rows field by field, each under its collation (BINARY past the given ones). -/
def cmpRowsColl (colls : Array Collation) (a b : Row) : Ordering :=
  go 0 (max a.size b.size)
where
  go (k : Nat) : Nat → Ordering
    | 0 => compare a.size b.size
    | f+1 => match cmpValues (colls.getD k .binary) (a.getD k .null) (b.getD k .null) with
      | .eq => go (k+1) f
      | o => o

def cmpRows (a b : Row) : Ordering := cmpRowsColl #[] a b

/-- Appends the merge of `src[i, mid)` and `src[j, hi)` to `dst`; on a tie the left element goes first. -/
@[specialize] def mergeRuns (cmp : α → α → Ordering) (src : Array α) (mid hi : Nat) (i j : Nat) (dst : Array α) : Nat → Array α
  | 0 => dst
  | f+1 =>
    if h : i < mid ∧ j < hi ∧ i < src.size ∧ j < src.size then
      let x := src[i]'h.2.2.1
      let y := src[j]'h.2.2.2
      if cmp y x == .lt then mergeRuns cmp src mid hi i (j+1) (dst.push y) f else mergeRuns cmp src mid hi (i+1) j (dst.push x) f
    else dst ++ src.extract i mid ++ src.extract j hi

/-- Merges neighbouring runs of `w` elements (the last may be shorter), then runs of `2w`, until one run is left. -/
@[specialize] def mergePasses (cmp : α → α → Ordering) (src : Array α) (w : Nat) : Nat → Array α
  | 0 => src
  | f+1 =>
    let n := src.size
    if w ≥ n then src else
    let dst := ((n + 2 * w - 1) / (2 * w)).fold (fun k _ dst =>
      let lo := k * 2 * w
      let mid := min (lo + w) n
      let hi := min (lo + 2 * w) n
      mergeRuns cmp src mid hi lo mid dst (hi - lo)) (Array.emptyWithCapacity n)
    mergePasses cmp dst (2 * w) f

/-- Stable sort (bottom-up merge sort). -/
@[specialize] def sortBy (xs : Array α) (cmp : α → α → Ordering) : Array α := mergePasses cmp xs 1 64

/-- The indexes of each row's first occurrence, in order (DISTINCT, UNION). -/
def firstOccurrences (rows : Array Row) (colls : Array Collation := #[]) : Array Nat :=
  let idx := sortBy (rows.mapIdx fun i r => (r, i)) fun (a, i) (b, j) => match cmpRowsColl colls a b with
    | .eq => compare i j
    | o => o
  let (keep, _) := idx.foldl (fun (keep, prev) (r, i) =>
    match prev with
    | some p => if cmpRowsColl colls p r == .eq then (keep, prev) else (keep.push i, some r)
    | none => (keep.push i, some r)) (#[], (none : Option Row))
  sortBy keep compare

/-- Rows sorted and deduplicated (a compound's result without ORDER BY comes out in this order, as sqlite's). -/
def sortedDistinct (rows : Array (Row × Row)) : Array (Row × Row) :=
  let s := sortBy rows fun a b => cmpRows a.1 b.1
  s.foldl (fun acc r => match acc.back? with
    | some p => if cmpRows p.1 r.1 == .eq then acc else acc.push r
    | none => acc.push r) #[]

def memRow (rows : Array (Row × Row)) (r : Row) : Bool :=
  -- rows sorted by cmpRows
  go 0 rows.size 64
where
  go (lo hi : Nat) : Nat → Bool
    | 0 => false
    | f+1 =>
      if lo ≥ hi then false else
      let mid := (lo + hi) / 2
      match cmpRows (rows.getD mid default).1 r with
      | .lt => go (mid+1) hi f
      | .gt => go lo mid f
      | .eq => true

/-- Binary search for `v` in values sorted under `coll`. -/
def memSorted (coll : Collation) (vals : Array Value) (v : Value) : Bool :=
  go 0 vals.size 64
where
  go (lo hi : Nat) : Nat → Bool
    | 0 => false
    | f+1 =>
      if lo ≥ hi then false else
      let mid := (lo + hi) / 2
      match cmpValues coll (vals.getD mid .null) v with
      | .lt => go (mid+1) hi f
      | .gt => go lo mid f
      | .eq => true

/-! ## Table and index scans -/

/-- Rows of a rowid range `[lo, hi]`. -/
def scanRange (p : Pager) (root : Pgno) (lo : Option Int64) (hi : Option Int64) : Array (Int64 × ByteArray) :=
  let c := match lo with
    | some l => BTree.Cursor.seekRowid p root l
    | none => BTree.Cursor.first p root
  go c #[] (BTree.entryBound p)
where
  go (c : BTree.Cursor) (acc : Array (Int64 × ByteArray)) : Nat → Array (Int64 × ByteArray)
    | 0 => acc
    | f+1 =>
      match c.row p with
      | none => acc
      | some (k, r) =>
        let stop : Bool := match hi with | some h => decide (k > h) | none => false
        if stop then acc
        else go (c.next p) (acc.push (k, r)) f

/-- The rowids of index entries from `probe` on, while their first `neq` fields equal the probe's and (when given) field
`neq` stays within `hi`. -/
def scanIndex (p : Pager) (root : Pgno) (ki : KeyInfo) (probe eqProbe : ByteArray) (neq : Nat)
    (hi : Option (Value × Bool)) : Array Int64 :=
  go (BTree.Cursor.seekKey p ki root probe) #[] (BTree.entryBound p)
where
  go (c : BTree.Cursor) (acc : Array Int64) : Nat → Array Int64
    | 0 => acc
    | f+1 =>
      match c.key p with
      | none => acc
      | some k =>
        if neq > 0 && cmpRecords ki k eqProbe != .eq then acc else
        let past : Bool := match hi with
          | some (h, incl) =>
            let v := recordColumn k neq
            if v.isNull then false else
            let o := cmpValues (ki.colls.getD neq .binary) v h
            o == .gt || (!incl && o == .eq)
          | none => false
        if past then acc else
        let rid := match recordColumn k (recordArity k - 1) with | .int r => r | _ => 0
        go (c.next p) (acc.push rid) f

/-- The rowid a range bound starts or ends at: none when the bound is not a number (the scan is then unbounded on that
side, and the WHERE clause decides). -/
def boundRowid (v : Value) (incl lower : Bool) : Option Int64 :=
  match Value.applyAff .numeric v with
  | .int i => some (if incl then i else if lower then i + 1 else i - 1)
  | .real f =>
    if f.isNaN || f.abs > 9.2e18 then none else
    let fl := f.floor
    if lower then some (if fl == f then (if incl then f.toInt64 else f.toInt64 + 1) else f.ceil.toInt64)
    else some (if fl == f then (if incl then f.toInt64 else f.toInt64 - 1) else fl.toInt64)
  | _ => none

mutual
def eval (env : Env) : CExpr → Nat → EM Value
  | _, 0 => .error "expression nested too deeply"
  | e, fuel+1 => match e with
  | .lit v => .ok v
  | .col d s => .ok (env.col d s)
  | .arith op a b => do
    let x ← eval env a fuel
    let y ← eval env b fuel
    return match op with
      | .concat => concatV x y
      | .bitAnd | .bitOr | .shl | .shr => bitop op x y
      | _ => arith op x y
  | .cmp op a b aff coll => do
    let x ← eval env a fuel
    let y ← eval env b fuel
    return compareV op aff coll x y
  | .and a b => do
    let x := (← eval env a fuel).truth?
    if x == some false then return boolV false
    let y := (← eval env b fuel).truth?
    return match x, y with
      | _, some false => boolV false
      | some true, some true => boolV true
      | _, _ => .null
  | .or a b => do
    let x := (← eval env a fuel).truth?
    if x == some true then return boolV true
    let y := (← eval env b fuel).truth?
    return match x, y with
      | _, some true => boolV true
      | some false, some false => boolV false
      | _, _ => .null
  | .not a => do return optBool ((← eval env a fuel).truth?.map (!·))
  | .neg a => do return negV (← eval env a fuel)
  | .bitNot a => do return match intOf (← eval env a fuel) with | some i => .int (~~~i) | none => .null
  | .fn name args => do
    if Json.isJsonFn name then
      let (v, _) ← evalJ env (.fn name args) fuel
      return v
    let vs ← evalArgs env args fuel
    evalFn env name vs
  | .agg i => .ok (env.aggs.getD i .null)
  | .case base whens els aff coll => do
    let b ← match base with
      | some x => do let v ← eval env x fuel; pure (some v)
      | none => pure none
    let r ← caseLoop env b whens 0 aff coll fuel
    match r with
    | some v => return v
    | none => match els with
      | some x => eval env x fuel
      | none => return .null
  | .cast x aff => do return castV aff (← eval env x fuel)
  | .inList x items neg aff coll => do
    if items.isEmpty then return boolV neg
    let v ← eval env x fuel
    if v.isNull then return .null
    let mut sawNull := false
    let mut found := false
    for it in items do
      let w ← eval env it fuel
      if w.isNull then sawNull := true
      else if isTrueV (compareV .eq aff coll v w) then found := true; break
    return if found then boolV (!neg) else if sawNull then .null else boolV neg
  | .inVals x vals hasNull neg aff coll => do
    let v ← eval env x fuel
    if v.isNull then return .null
    let v := Value.applyAff aff v
    if memSorted coll vals v then return boolV (!neg)
    return if hasNull then .null else boolV neg
  | .inSel x q neg aff coll _ => do
    let v ← eval env x fuel
    if v.isNull then return .null
    let rows ← runSel env q fuel
    let mut sawNull := false
    let mut found := false
    for r in rows do
      let w := r.getD 0 .null
      if w.isNull then sawNull := true
      else if isTrueV (compareV .eq aff coll v w) then found := true; break
    return if found then boolV (!neg) else if sawNull then .null else boolV neg
  | .exists q neg _ => do
    let rows ← runSel env q fuel
    return boolV (rows.isEmpty == neg)
  | .scalar q _ => do
    let rows ← runSel env q fuel
    return ((rows[0]?).bind (·[0]?)).getD .null
  | .matchE op x pat esc neg => do
    let v ← eval env x fuel
    let pv ← eval env pat fuel
    let ev ← match esc with
      | some e => do let r ← eval env e fuel; pure (some r)
      | none => pure none
    if v.isNull || pv.isNull then return .null
    if let some ev := ev then if ev.isNull then return .null
    let escB ← match ev with
      | some ev =>
        let b := ev.toBytes
        if b.size == 0 || charLen b 0 != b.size then throw "ESCAPE expression must be a single character"
        pure (some (rd b 0))
      | none => pure none
    let m := match op with
      | .glob => globMatch pv.toBytes v.toBytes
      | _ => likeMatch pv.toBytes v.toBytes escB
    return boolV (m != neg)
  | .isNull x neg => do return boolV ((← eval env x fuel).isNull != neg)
  | .inSelRow es q neg affs colls => do
    let vs ← es.mapM fun x => eval env x fuel
    let rows ← runSel env q fuel
    let mut sawNull := false
    let mut found := false
    for r in rows do
      let cs := vs.mapIdx fun i v => compareV .eq (affs.getD i .none) (colls.getD i .binary) v (r.getD i .null)
      if cs.all isTrueV then found := true; break
      -- no pair differs, but one is NULL: unknown
      if !cs.any (fun c => c.truth? == some false) && cs.any (·.isNull) then sawNull := true
    return if found then boolV (!neg) else if sawNull then .null else boolV neg
  | .win i => .ok (env.wins.getD i .null)
  | .raise k m => .error (raiseMsg k m)

/-- A value and whether it carries sqlite's JSON subtype (the direct result of a JSON function or aggregate). -/
def evalJ (env : Env) : CExpr → Nat → EM (Value × Bool)
  | _, 0 => .error "expression nested too deeply"
  | e, fuel+1 => match e with
  | .fn name args =>
    if Json.isJsonFn name then do
      let vs ← args.mapM fun a => evalJ env a fuel
      Json.callJ name (vs.map (·.1)) (vs.map (·.2))
    else if name == jsonValueTag then do
      let v ← eval env (args.getD 0 (.lit .null)) fuel
      let t ← eval env (args.getD 1 (.lit .null)) fuel
      pure (v, t == .text "array" || t == .text "object")
    else do let v ← eval env e fuel; pure (v, false)
  | .agg i => .ok (env.aggs.getD i .null, env.aggJson.getD i false)
  | e => do let v ← eval env e fuel; pure (v, false)

def evalArgs (env : Env) (args : Array CExpr) : Nat → EM (Array Value)
  | 0 => .error "expression nested too deeply"
  | fuel+1 => args.mapM fun a => eval env a fuel

def caseLoop (env : Env) (base : Option Value) (whens : Array (CExpr × CExpr)) (i : Nat) (aff : Aff) (coll : Collation) :
    Nat → EM (Option Value)
  | 0 => .ok none
  | fuel+1 =>
    match whens[i]? with
    | none => .ok none
    | some (w, t) => do
      let wv ← eval env w fuel
      let hit : Bool := match base with
        | some b => isTrueV (compareV .eq aff coll b wv)
        | none => wv.truth? == some true
      if hit then do let r ← eval env t fuel; return some r
      else caseLoop env base whens (i+1) aff coll fuel

/-- Whether every condition is true. -/
def allTrue (env : Env) (conds : Array CExpr) : Nat → EM Bool
  | 0 => .error "expression nested too deeply"
  | fuel+1 => do
    for c in conds do
      if (← eval env c fuel).truth? != some true then return false
    return true

/-- Uncorrelated subqueries run once: replaced by their result. -/
def hoist (env : Env) : CExpr → Nat → EM CExpr
  | e, 0 => .ok e
  | e, fuel+1 => match e with
  | .scalar q false => do
    let rows ← runSel env q fuel
    return .lit (((rows[0]?).bind (·[0]?)).getD .null)
  | .exists q neg false => do
    let rows ← runSel env q fuel
    return .lit (boolV (rows.isEmpty == neg))
  | .inSel x q neg aff coll false => do
    let x ← hoist env x fuel
    let rows ← runSel env q fuel
    let vs := rows.map (·.getD 0 .null)
    let hasNull := vs.any (·.isNull)
    let vs := sortBy ((vs.filter (!·.isNull)).map (Value.applyAff aff)) (cmpValues coll)
    return .inVals x vs hasNull neg aff coll
  | .arith op a b => do return .arith op (← hoist env a fuel) (← hoist env b fuel)
  | .cmp op a b aff coll => do return .cmp op (← hoist env a fuel) (← hoist env b fuel) aff coll
  | .and a b => do return .and (← hoist env a fuel) (← hoist env b fuel)
  | .or a b => do return .or (← hoist env a fuel) (← hoist env b fuel)
  | .not a => do return .not (← hoist env a fuel)
  | .neg a => do return .neg (← hoist env a fuel)
  | .fn n args => do return .fn n (← args.mapM fun a => hoist env a fuel)
  | .cast a aff => do return .cast (← hoist env a fuel) aff
  | .inList x items neg aff coll => do return .inList (← hoist env x fuel) (← items.mapM fun a => hoist env a fuel) neg aff coll
  | .matchE op x p esc neg => do
    let esc' ← match esc with
      | some x => do let r ← hoist env x fuel; pure (some r)
      | none => pure none
    return .matchE op (← hoist env x fuel) (← hoist env p fuel) esc' neg
  | .isNull x neg => do return .isNull (← hoist env x fuel) neg
  | e => .ok e

def hoistCore (env : Env) : CCore → Nat → EM CCore
  | c, 0 => .ok c
  | .values rows order, fuel+1 => do return .values (← rows.mapM fun r => r.mapM fun e => hoist env e fuel) order
  | .select srcs pre filters g gc h cols rc order aggs isAgg d w mm ws, fuel+1 => do
    let hs (es : Array CExpr) : EM (Array CExpr) := es.mapM fun e => hoist env e fuel
    let srcs ← srcs.mapM fun (s : CSource) => (match s with
      | .table r n ipk rc dv base acc left right lay on => do
        let acc : Access ← match acc with
          | .rowidEq e => do pure (Access.rowidEq (← hoist env e fuel))
          | .rowidIn items => do pure (Access.rowidIn (← hs items))
          | a => pure a
        return CSource.table r n ipk rc dv base acc left right lay (← hs on)
      | s => pure s : EM CSource)
    let h' ← match h with
      | some x => do let r ← hoist env x fuel; pure (some r)
      | none => pure none
    return .select srcs (← hs pre) (← filters.mapM hs) (← hs g) gc h' (← hs cols) rc (← hs order) aggs isAgg d w mm ws

/-- Runs a SELECT: its rows. -/
def runSel (env : Env) : CSel → Nat → EM (Array Row)
  | _, 0 => .error "query nested too deeply"
  | .mk ctes cores ops dirs limit offset _, fuel+1 => do
    -- WITH tables
    let mut env := env
    for .mk id q recursive in ctes do
      let rows ← if recursive then runRecursive env id q fuel else runSel env q fuel
      let cs := if env.ctes.size ≤ id then env.ctes ++ Array.replicate (id + 1 - env.ctes.size) #[] else env.ctes
      env := { env with ctes := cs.setIfInBounds id rows }
    let lim ← match limit with
      | some e => do
        let v ← eval env e fuel
        let i := Num.castToInt v
        pure (if i < 0 then none else some i.toNatClampNeg)
      | none => pure none
    let off ← match offset with
      | some e => do let v ← eval env e fuel; pure (Num.castToInt v).toNatClampNeg
      | none => pure 0
    let hint := if cores.size == 1 && dirs.isEmpty then lim.map (· + off) else none
    let mut acc : Array (Row × Row) := #[]
    let mut i := 0
    for core in cores do
      let core ← hoistCore env core fuel
      let rs ← runCore env core (if i == 0 then hint else none) fuel
      if i == 0 then acc := rs else
        match ops[i - 1]? with
        | some .unionAll => acc := acc ++ rs
        | some .union => acc := sortedDistinct (acc ++ rs)
        | some .intersect =>
          let r := sortedDistinct rs
          acc := (sortedDistinct acc).filter fun x => memRow r x.1
        | some .except =>
          let r := sortedDistinct rs
          acc := (sortedDistinct acc).filter fun x => !memRow r x.1
        | none => pure ()
      i := i + 1
    let sorted := if dirs.isEmpty then acc else sortBy acc fun a b => cmpKeys dirs a.2 b.2
    let page := sorted.extract off (match lim with | some l => off + l | none => sorted.size)
    return page.map (·.1)

/-- A recursive WITH table: the initial rows, then the recursive SELECT run on each queued row (sqlite's queue). -/
def runRecursive (env : Env) (id : Nat) : CSel → Nat → EM (Array Row)
  | _, 0 => .error "query nested too deeply"
  | .mk _ cores ops _ limit _ _, fuel+1 => do
    let some anchor := cores[0]? | return #[]
    let some recur := cores[1]? | return #[]
    let distinct := ops[0]? == some .union
    let lim ← match limit with
      | some e => do let v ← eval env e fuel; let i := Num.castToInt v; pure (if i < 0 then none else some i.toNatClampNeg)
      | none => pure none
    let anchor ← hoistCore env anchor fuel
    let init := (← runCore env anchor none fuel).map (·.1)
    let init := if distinct then (firstOccurrences init).map (init.getD · #[]) else init
    let mut result := init
    let mut qi := 0
    for _ in [0:1000000000] do
      if qi ≥ result.size then break
      if let some l := lim then if result.size ≥ l then break
      let row := result.getD qi #[]
      qi := qi + 1
      let cs := if env.ctes.size ≤ id then env.ctes ++ Array.replicate (id + 1 - env.ctes.size) #[] else env.ctes
      let env' := { env with ctes := cs.setIfInBounds id #[row] }
      let rs := (← runCore env' recur none fuel).map (·.1)
      for r in rs do
        if distinct && result.any (cmpRows · r == .eq) then continue
        result := result.push r
    return match lim with | some l => result.extract 0 l | none => result

/-- Runs one core: each result row with its ORDER BY keys. `hint`: enough rows (a LIMIT with no ORDER BY). -/
def runCore (env : Env) : CCore → Option Nat → Nat → EM (Array (Row × Row))
  | _, _, 0 => .error "query nested too deeply"
  | .values rows order, _, fuel+1 => do
    let mut out := #[]
    for r in rows do
      let vs ← r.mapM fun e => eval env e fuel
      out := out.push (vs, order.map (vs.getD · .null))
    return out
  | .select srcs pre filters groupBy gcolls having cols rcolls order aggs isAgg distinct width minmax wins, hint, fuel+1 => do
    let frame0 : Row := Array.replicate width .null
    unless ← allTrue (env.push frame0) pre fuel do
      if isAgg && groupBy.isEmpty then pure () else return #[]
    let preOk ← allTrue (env.push frame0) pre fuel
    -- FROM subqueries run once
    let subs ← srcs.mapM fun s => match s with
      | .sub q _ _ _ _ _ => do let r ← runSel env q fuel; pure (some r)
      | _ => pure none
    let rightIdx := srcs.findIdx? isRightOuter
    let hint := if isAgg || distinct || !order.isEmpty || !wins.isEmpty || rightIdx.isSome then none else hint
    let srcExprs := srcs.foldl (fun acc s => match s with
      | .table _ _ _ _ _ _ acc' _ _ _ on => acc ++ on ++ (match acc' with
        | .rowidEq e => #[e] | .rowidIn es => es
        | .rowidRange lo hi => (lo.map (·.1)).toArray ++ (hi.map (·.1)).toArray
        | .index _ _ eqs lo hi => eqs.map (·.1) ++ (lo.map (·.1)).toArray ++ (hi.map (·.1)).toArray
        | .full => #[])
      | .sub _ _ _ _ _ on | .cte _ _ _ _ _ on => acc ++ on
      | .tvf _ args _ _ _ _ on => acc ++ args ++ on) #[]
    let aggArgs := aggs.foldl (fun acc (.mk _ _ _ args _ f) => acc ++ args ++ f.toArray) #[]
    let winExprs := wins.foldl (fun acc (.mk _ _ _ args f part _ ord _ _ s fi _) =>
      acc ++ args ++ f.toArray ++ part ++ ord ++ boundExprs s ++ boundExprs fi) #[]
    let need := neededSlots width (cols ++ order ++ groupBy ++ having.toArray ++ pre ++ filters.foldl (· ++ ·) #[] ++ srcExprs
      ++ aggArgs ++ winExprs)
    -- a RIGHT or FULL JOIN's item: its rows are counted once, and the join marks those some earlier row matched
    let rightCount ← match rightIdx with
      | some r => do
        let (raw, cs) ← candidates env (srcs.getD r default) (subs.getD r none) frame0 fuel
        pure (if raw.isEmpty then cs.size else raw.size)
      | none => pure 0
    let (frames, matched) ← if !preOk then pure (#[], #[]) else if srcs.isEmpty then pure (#[frame0], #[])
      else joinFrom env srcs subs filters need 0 frame0 (#[], Array.replicate rightCount false) hint fuel
    -- then its rows nothing matched, with NULLs for the items before it
    let frames ← match rightIdx with
      | none => pure frames
      | some r => do
        let src := srcs.getD r default
        let (raw, cs) ← candidates env src (subs.getD r none) frame0 fuel
        let mut acc : Array Row × Array Bool := (frames, #[])
        for j in [0:rightCount] do
          if matched.getD j true then continue
          let fr := bindCand src need frame0 raw cs j
          let mut ok := true
          for k in [0:r+1] do
            unless ← allTrue (env.push fr) (filters.getD k #[]) fuel do ok := false; break
          if ok then acc ← joinFrom env srcs subs filters need (r+1) fr acc none fuel
        pure acc.1
    -- each result row's environment: its frame, or (aggregates) its group's
    let envs : Array Env ← if !isAgg then pure (frames.map env.push) else do
      -- groups: consecutive runs of equal GROUP BY keys after a stable sort
      let groups ← if groupBy.isEmpty then pure #[frames] else do
        let keyed ← frames.mapM fun fr => do
          let ks ← groupBy.mapM fun g => eval (env.push fr) g fuel
          pure (ks, fr)
        let sorted := sortBy keyed fun a b => cmpRowsColl gcolls a.1 b.1
        let gs := sorted.foldl (fun (gs : Array (Row × Array Row)) (k, fr) =>
          match gs.back? with
          | some (pk, g) => if cmpRowsColl gcolls pk k == .eq then gs.pop.push (pk, g.push fr) else gs.push (k, #[fr])
          | none => gs.push (k, #[fr])) #[]
        pure (gs.map (·.2))
      let mut out : Array Env := #[]
      for g in groups do
        -- step every aggregate over the group's rows
        let mut accs : Array AggAcc := aggs.map fun _ => {}
        let mut i := 0
        for fr in g do
          let e := env.push fr
          let mut j := 0
          for .mk name dist star args coll flt in aggs do
            -- a FILTER (WHERE f) skips the rows f is not true for
            if let some f := flt then
              if !isTrueV (← eval e f fuel) then
                j := j + 1
                continue
            -- (a JSON aggregate sees which arguments are JSON)
            let vjs ← if Json.isJsonAgg name then args.mapM fun a => evalJ e a fuel
              else do let vs ← args.mapM fun a => eval e a fuel; pure (vs.map fun v => (v, false))
            let vs := vjs.map (·.1)
            -- taken out of the array first, so it is updated in place
            let acc := accs.getD j {}
            accs := accs.setIfInBounds j {}
            let acc := if dist then (if vs.any (·.isNull) then acc else
                { acc with seen := acc.seen.push vs, seenJ := if Json.isJsonAgg name then acc.seenJ.push (vjs.map (·.2)) else acc.seenJ })
              else if Json.isJsonAgg name then { acc with json := Json.aggStep name acc.json vs (vjs.map (·.2)) }
              else aggStep name star coll acc vs i
            accs := accs.setIfInBounds j acc
            j := j + 1
          i := i + 1
        let mut vals := #[]
        let mut j := 0
        for .mk name dist star _ coll _ in aggs do
          let acc := accs.getD j {}
          let acc := if dist then
              (firstOccurrences acc.seen).foldl (fun a k =>
                if Json.isJsonAgg name then { a with json := Json.aggStep name a.json (acc.seen.getD k #[]) (acc.seenJ.getD k #[]) }
                else aggStep name star coll a (acc.seen.getD k #[]) 0) ({} : AggAcc)
            else acc
          vals := vals.push (← aggFinal name acc)
          accs := accs.setIfInBounds j acc
          j := j + 1
        let rep : Row := match minmax with
          | some (k, _) => g.getD (accs.getD k {}).bestAt frame0
          -- sqlite reads bare columns from a group's first row (with no GROUP BY, the last)
          | none => if groupBy.isEmpty then g.back?.getD frame0 else g[0]?.getD frame0
        let e := { (env.push rep) with aggs := vals, aggJson := aggs.map fun (.mk n _ _ _ _ _) => Json.isJsonAgg n }
        if let some h := having then
          if (← eval e h fuel).truth? != some true then continue
        out := out.push e
      pure out
    -- window functions, over all the result rows
    let winCols ← wins.mapM fun w => winColumn envs w fuel
    let mut out := #[]
    for i in [0:envs.size] do
      let e := { (envs.getD i env) with wins := winCols.map (·.getD i .null) }
      let vs ← cols.mapM fun c => eval e c fuel
      let ks ← order.mapM fun c => eval e c fuel
      out := out.push (vs, ks)
    if distinct then
      let rows := out.map (·.1)
      return (firstOccurrences rows rcolls).map (out.getD · default)
    return out

/-- A window function's value for each result row: rows ordered by partition and ORDER BY keys, peers grouped, and the
frame of each row found (ROWS, RANGE or GROUPS, with EXCLUDE). -/
def winColumn (envs : Array Env) (w : CWin) : Nat → EM (Array Value)
  | 0 => .error "query nested too deeply"
  | fuel+1 => do
    let .mk name distinct star args filter part pcolls ord dirs units start finish excl := w
    let n := envs.size
    let pk ← envs.mapM fun e => part.mapM fun x => eval e x fuel
    let ok ← envs.mapM fun e => ord.mapM fun x => eval e x fuel
    let av ← envs.mapM fun e => args.mapM fun x => eval e x fuel
    let isJ := Json.isJsonAgg name
    let aj ← if isJ then envs.mapM fun e => args.mapM fun x => do pure (← evalJ e x fuel).2 else pure #[]
    -- one row into an aggregate (a JSON one with its arguments' subtypes)
    let stepW (acc : AggAcc) (row : Nat) (vs : Array Value) (at_ : Nat) : AggAcc :=
      if isJ then { acc with json := Json.aggStep name acc.json vs (aj.getD row #[]) } else aggStep name star .binary acc vs at_
    let fv ← envs.mapM fun e => match filter with
      | some f => do pure ((← eval e f fuel).truth? == some true)
      | none => pure true
    let offs ← envs.mapM fun e => do
      let o (b : CBound) : EM Int := match b with
        | .preceding x | .following x => do
          let v ← eval e x fuel
          match v with
          | .int i => if i < 0 then throw "frame starting offset must be a non-negative integer" else pure i.toInt
          | .real r => if r < 0 then throw "frame starting offset must be a non-negative number" else pure r.toInt64.toInt
          | _ => throw "frame starting offset must be a non-negative integer"
        | _ => pure 0
      pure (← o start, ← o finish)
    let rowsInOrder := sortBy ((List.range n).toArray) fun a b =>
      match cmpRowsColl pcolls (pk.getD a #[]) (pk.getD b #[]) with
      | .eq => match cmpKeys dirs (ok.getD a #[]) (ok.getD b #[]) with
        | .eq => compare a b
        | o => o
      | o => o
    let parts : Array (Array Nat) := rowsInOrder.foldl (fun ps i => match ps.back? with
      | some p => if cmpRowsColl pcolls (pk.getD (p.getD 0 0) #[]) (pk.getD i #[]) == .eq then ps.pop.push (p.push i) else ps.push #[i]
      | none => #[#[i]]) #[]
    let mut res := Array.replicate n Value.null
    for p in parts do
      let m := p.size
      -- peer groups: each position's group, each group's first and last position
      let (grp, firsts) := (List.range m).foldl (fun (acc : Array Nat × Array Nat) q =>
        let newGroup := q == 0 || cmpKeys dirs (ok.getD (p.getD (q-1) 0) #[]) (ok.getD (p.getD q 0) #[]) != .eq
        let firsts := if newGroup then acc.2.push q else acc.2
        (acc.1.push (firsts.size - 1), firsts)) (#[], #[])
      let lastOf (g : Nat) : Nat := (firsts.getD (g+1) m) - 1
      let firstOfI (g : Int) : Int := if g < 0 then 0 else if g ≥ firsts.size then m else (firsts.getD g.toNat m : Int)
      let lastOfI (g : Int) : Int := if g < 0 then -1 else if g ≥ firsts.size then (m : Int) - 1 else (lastOf g.toNat : Int)
      let keyOf (q : Nat) : Value := (ok.getD (p.getD q 0) #[]).getD 0 .null
      -- the frame of position q, as positions [lo, hi]
      let frameOf (q : Nat) : Int × Int :=
        let (so, fo) := offs.getD (p.getD q 0) (0, 0)
        let g : Int := grp.getD q 0
        let qi : Int := q
        match units with
        | .rows =>
          (match start with
            | .unboundedPreceding => 0 | .preceding _ => qi - so | .currentRow => qi | .following _ => qi + so
            | .unboundedFollowing => m,
           match finish with
            | .unboundedPreceding => -1 | .preceding _ => qi - fo | .currentRow => qi | .following _ => qi + fo
            | .unboundedFollowing => (m : Int) - 1)
        | .groups =>
          (match start with
            | .unboundedPreceding => 0 | .preceding _ => firstOfI (g - so) | .currentRow => firstOfI g
            | .following _ => firstOfI (g + so) | .unboundedFollowing => m,
           match finish with
            | .unboundedPreceding => -1 | .preceding _ => lastOfI (g - fo) | .currentRow => lastOfI g
            | .following _ => lastOfI (g + fo) | .unboundedFollowing => (m : Int) - 1)
        | .range =>
          -- numeric offsets on the single ORDER BY key (NULL keys: the peers)
          let k := keyOf q
          let desc := (dirs.getD 0 (false, true, .binary)).1
          let within (lim : Float) (lower : Bool) (r : Nat) : Bool :=
            let v := keyOf r
            match v with
            | .int _ | .real _ =>
              let x := toF v
              if lower then (if desc then x ≤ lim else x ≥ lim) else (if desc then x ≥ lim else x ≤ lim)
            | _ => false
          let lowBy (d : Float) : Int :=
            match k with
            | .int _ | .real _ =>
              let lim := if desc then toF k + d else toF k - d
              ((List.range m).find? (within lim true)).map (Int.ofNat) |>.getD m
            | _ => firstOfI g
          let highBy (d : Float) : Int :=
            match k with
            | .int _ | .real _ =>
              let lim := if desc then toF k - d else toF k + d
              (((List.range m).reverse.find? (within lim false)).map Int.ofNat).getD (-1)
            | _ => lastOfI g
          (match start with
            | .unboundedPreceding => 0 | .preceding _ => lowBy (Float.ofInt so) | .currentRow => firstOfI g
            | .following _ => lowBy (-(Float.ofInt so)) | .unboundedFollowing => m,
           match finish with
            | .unboundedPreceding => -1 | .preceding _ => highBy (-(Float.ofInt fo)) | .currentRow => lastOfI g
            | .following _ => highBy (Float.ofInt fo) | .unboundedFollowing => (m : Int) - 1)
      -- the positions of the frame of q, after EXCLUDE
      let framePositions (q : Nat) : Array Nat :=
        let (lo, hi) := frameOf q
        let lo := max lo 0
        let hi := min hi ((m : Int) - 1)
        if hi < lo then #[] else
        let all := (List.range (hi - lo + 1).toNat).toArray.map fun d => lo.toNat + d
        match excl with
        | .noOthers => all
        | .currentRow => all.filter (· != q)
        | .group => all.filter fun r => grp.getD r 0 != grp.getD q 0
        | .ties => all.filter fun r => r == q || grp.getD r 0 != grp.getD q 0
      let isAggW := ["COUNT", "SUM", "TOTAL", "AVG", "MIN", "MAX", "GROUP_CONCAT", "STRING_AGG", "JSON_GROUP_ARRAY",
        "JSON_GROUP_OBJECT", "MEDIAN", "PERCENTILE", "PERCENTILE_CONT", "PERCENTILE_DISC"].contains name
      -- a running aggregate when the frame only grows (UNBOUNDED PRECEDING, nothing excluded, no DISTINCT)
      let running := isAggW && start matches .unboundedPreceding && excl == .noOthers && !distinct
      let mut acc : AggAcc := {}
      let mut upto : Nat := 0
      for q in [0:m] do
        let row := p.getD q 0
        let a := av.getD row #[]
        let v ← match name with
          | "ROW_NUMBER" => pure (.int (q + 1).toInt64)
          | "RANK" => pure (.int ((firsts.getD (grp.getD q 0) 0) + 1).toInt64)
          | "DENSE_RANK" => pure (.int ((grp.getD q 0) + 1).toInt64)
          | "PERCENT_RANK" => pure (.real (if m ≤ 1 then 0 else (firsts.getD (grp.getD q 0) 0).toFloat / (m - 1).toFloat))
          | "CUME_DIST" => pure (.real ((lastOf (grp.getD q 0) + 1).toFloat / m.toFloat))
          | "NTILE" => do
            let nb := Num.castToInt (a.getD 0 .null)
            if nb ≤ 0 then throw "argument of ntile must be a positive integer"
            let nb := nb.toNatClampNeg
            let per := m / nb
            let extra := m % nb
            let big := extra * (per + 1)
            pure (.int (if q < big then q / (per + 1) + 1 else if per == 0 then q + 1 else extra + (q - big) / per + 1).toInt64)
          | "LAG" | "LEAD" => do
            let off : Int := if a.size > 1 then (Num.castToInt (a.getD 1 .null)).toInt else 1
            let t : Int := if name == "LAG" then (q : Int) - off else (q : Int) + off
            pure (if t ≥ 0 && t < m then ((av.getD (p.getD t.toNat 0) #[]).getD 0 .null) else a.getD 2 .null)
          | "FIRST_VALUE" | "LAST_VALUE" | "NTH_VALUE" => do
            let fp := framePositions q
            match name with
            | "FIRST_VALUE" => pure ((fp[0]?.map fun r => (av.getD (p.getD r 0) #[]).getD 0 .null).getD .null)
            | "LAST_VALUE" => pure ((fp.back?.map fun r => (av.getD (p.getD r 0) #[]).getD 0 .null).getD .null)
            | _ =>
              let k := Num.castToInt (a.getD 1 .null)
              if k ≤ 0 then throw "second argument to nth_value must be a positive integer"
              pure ((fp[k.toNatClampNeg - 1]?.map fun r => (av.getD (p.getD r 0) #[]).getD 0 .null).getD .null)
          | _ =>
            if running then do
              let (_, hi) := frameOf q
              let hi := min hi ((m : Int) - 1)
              -- the frame [0, hi] grows with q: step the rows it gained
              for r in [upto:(hi + 1).toNat] do
                let rr := p.getD r 0
                if fv.getD rr true then acc := stepW acc rr (av.getD rr #[]) r
              upto := max upto (hi + 1).toNat
              aggFinal name acc
            else do
              let fp := framePositions q
              let rowsIn := (fp.filter fun r => fv.getD (p.getD r 0) true).map (p.getD · 0)
              let rowsIn := if distinct then
                  let nn := rowsIn.filter fun rr => !(av.getD rr #[]).any (·.isNull)
                  let vals := nn.map (av.getD · #[])
                  (firstOccurrences vals).map (nn.getD · 0)
                else rowsIn
              aggFinal name (rowsIn.foldl (fun acc rr => stepW acc rr (av.getD rr #[]) 0) {})
        res := res.setIfInBounds row v
    return res

/-- The nested-loop join from FROM item `i` on: each candidate row of the item bound into the frame, its conditions
checked, then the later items; a LEFT JOIN's item with no match binds NULLs; a RIGHT JOIN's matched rows are marked. -/
def joinFrom (env : Env) (srcs : Array CSource) (subs : Array (Option (Array Row))) (filters : Array (Array CExpr))
    (need : Array Bool) (i : Nat) (frame : Row) (acc : Array Row × Array Bool) (hint : Option Nat) :
    Nat → EM (Array Row × Array Bool)
  | 0 => .error "query nested too deeply"
  | fuel+1 => do
    let some src := srcs[i]? | return (acc.1.push frame, acc.2)
    let (base, n, left, right, on) := match src with
      | .table _ n _ _ _ base _ left right _ on => (base, n + 1, left, right, on)
      | .sub _ n base left right on => (base, n, left, right, on)
      | .cte _ n base left right on => (base, n, left, right, on)
      | .tvf _ _ n base left right on => (base, n, left, right, on)
    let (raw, cands) ← candidates env src (subs.getD i none) frame fuel
    let conds := filters.getD i #[]
    let mut acc := acc
    let mut matched := false
    let count := if raw.isEmpty then cands.size else raw.size
    for j in [0:count] do
      if let some h := hint then if acc.1.size ≥ h then break
      let fr := bindCand src need frame raw cands j
      let e := env.push fr
      if left || right then
        unless ← allTrue e on fuel do continue
      matched := true
      if right then acc := (acc.1, acc.2.setIfInBounds j true)
      if ← allTrue e conds fuel then
        acc ← joinFrom env srcs subs filters need (i+1) fr acc hint fuel
    if left && !matched then
      let fr := n.fold (fun k _ (fr : Row) => fr.setIfInBounds (base + k) .null) frame
      if ← allTrue (env.push fr) conds fuel then
        acc ← joinFrom env srcs subs filters need (i+1) fr acc hint fuel
    return acc

/-- The rows a FROM item offers for the current frame: a table's (rowid, record) pairs through its access path, or a
subquery's or WITH table's rows. -/
def candidates (env : Env) (src : CSource) (sub : Option (Array Row)) (frame : Row) :
    Nat → EM (Array (Int64 × ByteArray) × Array Row)
  | 0 => .error "query nested too deeply"
  | fuel+1 =>
    match src with
    | .sub _ _ _ _ _ _ => .ok (#[], sub.getD #[])
    | .cte id _ _ _ _ _ => .ok (#[], env.ctes.getD id #[])
    | .tvf fn args _ _ _ _ _ => do
      let vs ← args.mapM fun x => eval (env.push frame) x fuel
      if fn.startsWith "pragma_" then
        return (#[], ((schemaPragma env.schema (fn.drop 7).toString ((vs.getD 0 .null).toText)).map (·.2)).getD #[])
      let rows ← tvfRows (fn == "json_tree") (vs.getD 0 .null) vs[1]?
      return (#[], rows)
    | .table root n _ realCols _ _ access _ _ layout _ => do
      let p := env.pager
      -- a WITHOUT ROWID table: its index-format tree's records, each field placed in its column
      if !layout.isEmpty then
        return (#[], BTree.foldIndex p root #[] fun acc r => acc.push (worRow n layout realCols r))
      let e := env.push frame
      let dec (rs : Array (Int64 × ByteArray)) : Array (Int64 × ByteArray) × Array Row := (rs, #[])
      let find (k : Int64) : Array (Int64 × ByteArray) :=
        match BTree.tableFind p root k with | some c => #[(k, c.payload)] | none => #[]
      match access with
      | .full => return dec (BTree.foldTable p root #[] fun acc k r => acc.push (k, r))
      | .rowidEq x => do
        let v ← eval e x fuel
        return match toRowid? v with | some k => dec (find k) | none => (#[], #[])
      | .rowidIn items => do
        let vs ← items.mapM fun x => eval e x fuel
        let ks := sortBy (vs.filterMap toRowid?) compare
        let ks := ks.foldl (fun acc k => if acc.back? == some k then acc else acc.push k) #[]
        return dec (ks.foldl (fun acc k => acc ++ find k) #[])
      | .rowidRange lo hi => do
        let lo' ← match lo with
          | some (x, incl) => do let v ← eval e x fuel; pure (boundRowid v incl true)
          | none => pure none
        let hi' ← match hi with
          | some (x, incl) => do let v ← eval e x fuel; pure (boundRowid v incl false)
          | none => pure none
        return dec (scanRange p root lo' hi')
      | .index iroot ki eqs lo hi => do
        let mut eqv : Array Value := #[]
        for (x, aff) in eqs do
          let v := Value.applyAff aff (← eval e x fuel)
          if v.isNull then return (#[], #[])
          eqv := eqv.push v
        let lov ← match lo with
          | some (x, _, aff) => do
            let v := Value.applyAff aff (← eval e x fuel)
            pure (if v.isNull then none else some v)
          | none => pure none
        let hiv ← match hi with
          | some (x, incl, aff) => do
            let v := Value.applyAff aff (← eval e x fuel)
            pure (if v.isNull then none else some (v, incl))
          | none => pure none
        let eqProbe := encodeRecord eqv
        let probe := match lov with | some v => encodeRecord (eqv.push v) | none => eqProbe
        -- with no lower bound, NULL entries (which sort first) are skipped by starting after them
        let probe := if lov.isNone && hiv.isSome then encodeRecord (eqv.push (.int (-9223372036854775808)) |>.pop |>.push (Value.real (-1.0/0.0))) else probe
        let rids := scanIndex p iroot ki probe eqProbe eqv.size hiv
        return dec (rids.foldl (fun acc k => acc ++ find k) #[])
end

end LSql

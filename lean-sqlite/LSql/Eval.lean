import LSql.Compile
import LSql.BTree
import LSql.DateTime
import LSql.Json
import Std.Data.TreeMap
import Std.Data.TreeSet
/-! Running compiled SELECTs (sqlite's VDBE role, over immutable state): expressions compiled once per query to
closures, the nested-loop join, aggregation, compound operators, ORDER BY and LIMIT. -/
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
/-- The current row's frame. -/
def top (env : Env) : Row := env.frames.getD (env.frames.size - 1) #[]
/-- The environment with its current row's frame changed by `f` (in place when neither is shared). -/
def modifyTop (env : Env) (f : Row → Row) : Env := { env with frames := env.frames.modify (env.frames.size - 1) f }
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
  let a := Value.applyCmpAff aff a
  let b := Value.applyCmpAff aff b
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

/-- A value as a rowid, if it equals one. -/
def toRowid? (v : Value) : Option Int64 :=
  match Value.applyAff .integer v with
  | .int i => some i
  | _ => none

/-- A LIMIT or OFFSET value as an integer (OP_MustBeInt): what an INTEGER column keeps of it, else a datatype mismatch. -/
def limitInt (v : Value) : EM Int64 :=
  match toRowid? v with
  | some i => pure i
  | none => .error "datatype mismatch"

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

/-! ## Compiled expressions

A core's expressions are compiled once per run into closures (the role of sqlite's VDBE program): operators, affinities,
collations and functions are decided once, literals converted once, and each row runs the closures. -/

/-- Compiled computations over an environment: a value (`CFn`), a truth value (`CTruth`, NULL as none), whether a
condition holds (`CPred`), or a value with whether it carries sqlite's JSON subtype (`CFnJ`). -/
abbrev CFn := Env → EM Value
abbrev CTruth := Env → EM (Option Bool)
abbrev CPred := Env → EM Bool
abbrev CFnJ := Env → EM (Value × Bool)

/-- How compiled code runs a subquery. -/
abbrev SubRun := Env → CSel → EM (Array Row)

/-- A scalar function, resolved from its name once per call site. -/
abbrev ScalarFn := Env → Array Value → EM Value

/-- A scalar function's body given its first three arguments (NULL past the end) and whether any argument is NULL. -/
def ScalarFn.of (f : Env → Array Value → Value → Value → Value → Bool → EM Value) : ScalarFn :=
  fun env a => f env a (a.getD 0 .null) (a.getD 1 .null) (a.getD 2 .null) (a.any (·.isNull))

set_option linter.unusedVariables false in
/-- The scalar functions (func.c). -/
def fnOf (name : String) : ScalarFn :=
  if name == jsonValueTag then fun _ a => .ok (a.getD 0 .null) else
  if DateTime.isDateFn name then fun env a => DateTime.call name a env.nowMs else
  match name with
  | "ABS" => ScalarFn.of fun env a x y z anyNull => absV x
  | "LENGTH" => ScalarFn.of fun env a x y z anyNull => .ok (match x with
    | .null => .null
    | .blob b => .int b.size.toInt64
    | v =>
      let t := v.toText.takeWhile (· != '\x00')
      .int (if hasEsc v.toText then charCount t.copy else t.positions.length).toInt64)
  | "OCTET_LENGTH" => ScalarFn.of fun env a x y z anyNull => .ok (match x with | .null => .null | v => .int v.toBytes.size.toInt64)
  | "LOWER" => ScalarFn.of fun env a x y z anyNull => .ok (match x with | .null => .null | v => .text (lowerAscii v.toText))
  | "UPPER" => ScalarFn.of fun env a x y z anyNull => .ok (match x with | .null => .null | v => .text (upperAscii v.toText))
  | "TYPEOF" => ScalarFn.of fun env a x y z anyNull => .ok (.text x.typeName)
  | "HEX" => ScalarFn.of fun env a x y z anyNull => .ok (.text (hexOf x.toBytes))
  | "QUOTE" => ScalarFn.of fun env a x y z anyNull => .ok (.text (quoteV x))
  | "UNICODE" => ScalarFn.of fun env a x y z anyNull => .ok (unicodeV x)
  | "CHAR" => ScalarFn.of fun env a x y z anyNull => .ok (charV a)
  | "COALESCE" => ScalarFn.of fun env a x y z anyNull => .ok ((a.find? (!·.isNull)).getD .null)
  | "IFNULL" => ScalarFn.of fun env a x y z anyNull => .ok (if x.isNull then y else x)
  | "NULLIF" => ScalarFn.of fun env a x y z anyNull => .ok (if !x.isNull && !y.isNull && cmpValues .binary x y == .eq then .null else x)
  | "IIF" | "IF" => ScalarFn.of fun env a x y z anyNull => .ok (if x.truth? == some true then y else z)
  | "INSTR" => ScalarFn.of fun env a x y z anyNull => .ok (instrV x y)
  | "SUBSTR" | "SUBSTRING" => ScalarFn.of fun env a x y z anyNull =>
    .ok (if x.isNull || y.isNull || (a.size > 2 && z.isNull) then .null
      else substrV x (Num.castToInt y) (if a.size > 2 then some (Num.castToInt z) else none))
  | "REPLACE" => ScalarFn.of fun env a x y z anyNull =>
    .ok (if anyNull then .null else
      let s := x.toText
      let f := y.toText
      if f.isEmpty then .text s else .text (canonText (s.replace f z.toText)))
  | "TRIM" | "LTRIM" | "RTRIM" => ScalarFn.of fun env a x y z anyNull =>
    .ok (if x.isNull || (a.size > 1 && y.isNull) then .null else
      let cs := if a.size > 1 then y.toText.toList else [' ']
      .text (trimChars x.toText cs (name != "RTRIM") (name != "LTRIM")))
  | "ROUND" => ScalarFn.of fun env a x y z anyNull => .ok (roundV x a[1]?)
  | "MIN" | "MAX" => ScalarFn.of fun env a x y z anyNull =>
    .ok (if anyNull then .null else
      a.foldl (fun (best : Value) v =>
        let o := cmpValues .binary v best
        if (name == "MIN" && o == .lt) || (name == "MAX" && o == .gt) then v else best) x)
  | "LIKE" => ScalarFn.of fun env a x y z anyNull =>
    if x.isNull || y.isNull || (a.size > 2 && z.isNull) then .ok .null else
    if a.size > 2 then
      match likeEscape z.toBytes with
      | some esc => .ok (boolV (likeMatch x.toBytes y.toBytes (some esc)))
      | none => .error "ESCAPE expression must be a single character"
    else .ok (boolV (likeMatch x.toBytes y.toBytes none))
  | "GLOB" => ScalarFn.of fun env a x y z anyNull => .ok (if anyNull then .null else boolV (globMatch x.toBytes y.toBytes))
  | "PRINTF" | "FORMAT" => ScalarFn.of fun env a x y z anyNull => .ok (if x.isNull then .null else .text (Num.printf x.toText (a.toList.drop 1)))
  | "CONCAT" => ScalarFn.of fun env a x y z anyNull => .ok (.text (canonText (a.foldl (fun s v => if v.isNull then s else s ++ v.toText) "")))
  | "CONCAT_WS" => ScalarFn.of fun env a x y z anyNull =>
    .ok (if x.isNull then .null else
      let parts := (a.toList.drop 1).filter (!·.isNull) |>.map (·.toText)
      .text (canonText (x.toText.intercalate parts)))
  | "LAST_INSERT_ROWID" => ScalarFn.of fun env a x y z anyNull => .ok (.int env.lastRowid)
  | "CHANGES" => ScalarFn.of fun env a x y z anyNull => .ok (.int env.changes)
  | "TOTAL_CHANGES" => ScalarFn.of fun env a x y z anyNull => .ok (.int env.totalChanges)
  | "SQLITE_VERSION" => ScalarFn.of fun env a x y z anyNull => .ok (.text "3.54.0")
  | "SQLITE_SOURCE_ID" => ScalarFn.of fun env a x y z anyNull => .ok (.text "lean-sqlite")
  | "SIGN" => ScalarFn.of fun env a x y z anyNull => .ok (signV x)
  | "SQRT" => ScalarFn.of fun env a x y z anyNull => .ok (math1 (fun f => if f < 0 then 0.0/0.0 else f.sqrt) x)
  | "EXP" => ScalarFn.of fun env a x y z anyNull => .ok (math1 Float.exp x)
  | "LN" => ScalarFn.of fun env a x y z anyNull => .ok (math1 (fun f => if f ≤ 0 then 0.0/0.0 else f.log) x)
  | "LOG10" => ScalarFn.of fun env a x y z anyNull => .ok (math1 (fun f => if f ≤ 0 then 0.0/0.0 else f.log10) x)
  | "LOG2" => ScalarFn.of fun env a x y z anyNull => .ok (math1 (fun f => if f ≤ 0 then 0.0/0.0 else f.log2) x)
  | "LOG" => ScalarFn.of fun env a x y z anyNull =>
    if a.size == 1 then .ok (math1 (fun f => if f ≤ 0 then 0.0/0.0 else f.log10) x) else
    match numOf x, numOf y with
    | .null, _ | _, .null => .ok .null
    | b, v => let b := toF b; let v := toF v
      .ok (if b ≤ 0 || b == 1 || v ≤ 0 then .null else realV (v.log / b.log))
  | "CEIL" | "CEILING" => ScalarFn.of fun env a x y z anyNull => .ok (intRound Float.ceil x)
  | "FLOOR" => ScalarFn.of fun env a x y z anyNull => .ok (intRound Float.floor x)
  | "TRUNC" => ScalarFn.of fun env a x y z anyNull => .ok (intRound (fun f => if f ≥ 0 then f.floor else f.ceil) x)
  | "SIN" => ScalarFn.of fun env a x y z anyNull => .ok (math1 Float.sin x)
  | "COS" => ScalarFn.of fun env a x y z anyNull => .ok (math1 Float.cos x)
  | "TAN" => ScalarFn.of fun env a x y z anyNull => .ok (math1 Float.tan x)
  | "ASIN" => ScalarFn.of fun env a x y z anyNull => .ok (math1 Float.asin x)
  | "ACOS" => ScalarFn.of fun env a x y z anyNull => .ok (math1 Float.acos x)
  | "ATAN" => ScalarFn.of fun env a x y z anyNull => .ok (math1 Float.atan x)
  | "SINH" => ScalarFn.of fun env a x y z anyNull => .ok (math1 Float.sinh x)
  | "COSH" => ScalarFn.of fun env a x y z anyNull => .ok (math1 Float.cosh x)
  | "TANH" => ScalarFn.of fun env a x y z anyNull => .ok (math1 Float.tanh x)
  | "ASINH" => ScalarFn.of fun env a x y z anyNull => .ok (math1 Float.asinh x)
  | "ACOSH" => ScalarFn.of fun env a x y z anyNull => .ok (math1 Float.acosh x)
  | "ATANH" => ScalarFn.of fun env a x y z anyNull => .ok (math1 Float.atanh x)
  | "DEGREES" => ScalarFn.of fun env a x y z anyNull => .ok (math1 (fun f => f * 180.0 / 3.141592653589793) x)
  | "RADIANS" => ScalarFn.of fun env a x y z anyNull => .ok (math1 (fun f => f * 3.141592653589793 / 180.0) x)
  | "PI" => ScalarFn.of fun env a x y z anyNull => .ok (.real 3.141592653589793)
  | "POW" | "POWER" => ScalarFn.of fun env a x y z anyNull =>
    .ok (match numOf x, numOf y with | .null, _ | _, .null => .null | b, e => realV (Float.pow (toF b) (toF e)))
  | "ATAN2" => ScalarFn.of fun env a x y z anyNull =>
    .ok (match numOf x, numOf y with | .null, _ | _, .null => .null | b, e => realV (Float.atan2 (toF b) (toF e)))
  | "MOD" => ScalarFn.of fun env a x y z anyNull =>
    .ok (match numOf x, numOf y with
      | .null, _ | _, .null => .null
      | b, e => let d := toF e; if d == 0 then .null else
        let q := toF b / d
        let t := if q ≥ 0 then q.floor else q.ceil
        realV (toF b - t * d))
  | "ZEROBLOB" => ScalarFn.of fun env a x y z anyNull => .ok (.blob (pushZeros ByteArray.empty (Num.castToInt x).toNatClampNeg))
  | "UNHEX" => ScalarFn.of fun env a x y z anyNull => .ok (unhexV x)
  | "LIKELY" | "UNLIKELY" | "LIKELIHOOD" => ScalarFn.of fun env a x y z anyNull => .ok x
  | "SOUNDEX" => ScalarFn.of fun env a x y z anyNull => .ok (.text (soundex x))
  | "RANDOM" => ScalarFn.of fun env a x y z anyNull =>
    -- a pseudo-random number: the statement's clock, the call site (its last argument) and the current row, mixed
    .ok (.int (splitmix (seedOf env (Num.castToInt (a.getD 0 .null)))).toInt64)
  | "RANDOMBLOB" => ScalarFn.of fun env a x y z anyNull =>
    let n := max 1 (Num.castToInt x).toNatClampNeg
    let s0 := seedOf env (Num.castToInt (a.getD 1 .null))
    let (b, _) := n.fold (fun _ _ (acc : ByteArray × UInt64) =>
      let s := splitmix acc.2
      (acc.1.push s.toUInt8, s)) (ByteArray.empty, s0)
    .ok (.blob b)
  | _ => ScalarFn.of fun _ _ _ _ _ _ => .error s!"no such function: {name}"

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

/-- One row into an aggregate: its accumulator, the row's arguments and the row's position in its group. -/
abbrev AggStepFn := AggAcc → Array Value → Nat → AggAcc

/-- min() and max(): `better` is the ordering of a new best value against the current one. -/
def minMaxStep (better : Ordering) (coll : Collation) : AggStepFn := fun acc args at_ =>
  let x := args.getD 0 .null
  if x.isNull then acc else
  if !acc.any then { acc with best := x, bestAt := at_, any := true } else
  if cmpValues coll x acc.best == better then { acc with best := x, bestAt := at_ } else acc

/-- The step of aggregate `name`, resolved once per aggregate. -/
def aggStepOf (name : String) (star : Bool) (coll : Collation) : AggStepFn :=
  if Json.isJsonAgg name then fun acc args _ => { acc with json := Json.aggStep name acc.json args (args.map fun _ => false) } else
  if isPercentile name then fun acc args _ => percentStep name acc args else
  match name with
  | "COUNT" => fun acc args _ => if star || !(args.getD 0 .null).isNull then { acc with n := acc.n + 1 } else acc
  | "SUM" | "TOTAL" | "AVG" => fun acc args _ =>
    let x := args.getD 0 .null
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
  | "MIN" | "MAX" => minMaxStep (if name == "MIN" then .lt else .gt) coll
  | _ => fun acc args _ => -- GROUP_CONCAT, STRING_AGG
    let x := args.getD 0 .null
    if x.isNull then acc else
    let sep := if args.size > 1 then (args.getD 1 .null).toText else ","
    if acc.any then { acc with str := acc.str ++ sep ++ x.toText } else { acc with str := x.toText, any := true }

def aggStep (name : String) (star : Bool) (coll : Collation) (acc : AggAcc) (args : Array Value) (at_ : Nat) : AggAcc :=
  aggStepOf name star coll acc args at_

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
  | _ => .ok (if acc.any then .text (canonText acc.str) else .null)

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
column's integers are reals, a column the record lacks has its default), then the rowid (when `need` marks its slot). -/
def fillRow (frame : Row) (base n : Nat) (ipk : Option Nat) (realCols : Array Bool) (defaults : Array Value)
    (need : Array Bool) (rowid : Int64) (rec_ : ByteArray) : Row :=
  let upto := lastNeeded n
  let (hs, k) := getVarint rec_ 0
  let frame := go frame upto hs.toNat k hs.toNat 0 (n + 1)
  let frame := match ipk with
    | some i => if need.getD (base + i) true then frame.setIfInBounds (base + i) (.int rowid) else frame
    | none => frame
  if need.getD (base + n) true then frame.setIfInBounds (base + n) (.int rowid) else frame
where
  /-- one past the last column `need` marks -/
  lastNeeded : Nat → Nat
    | 0 => 0
    | i+1 => if need.getD (base + i) true then i + 1 else lastNeeded i
  go (fr : Row) (upto hs pos body i : Nat) : Nat → Row
    | 0 => fr
    | f+1 =>
      if i ≥ upto then fr else
      if pos ≥ hs then
        -- columns past the record's end (added by ALTER TABLE): their defaults
        go (if need.getD (base + i) true then fr.setIfInBounds (base + i) (defaults.getD i .null) else fr) upto hs pos body (i+1) f
      else
      let (t, l) := getVarint rec_ pos
      let fr := if need.getD (base + i) true then
          let v := decodeField rec_ body t
          let v := match v with | .int x => if realCols.getD i false then .real x.toFloat else v | v => v
          fr.setIfInBounds (base + i) v
        else fr
      go fr upto hs (pos + l) (body + serialLen t) (i+1) f

/-- A WITHOUT ROWID table's record as a row of slots: each field in its column (`layout`), a field the record lacks (a column
added by ALTER TABLE) its default, the rowid slot NULL. -/
def worRow (n : Nat) (layout : Array Nat) (realCols : Array Bool) (defaults : Array Value) (rec_ : ByteArray) : Row :=
  let vs := decodeRecord rec_
  layout.size.fold (fun k _ (row : Row) =>
    let c := layout.getD k 0
    let v := vs.getD k (defaults.getD c .null)
    let v := match v with | .int x => if realCols.getD c false then .real x.toFloat else v | v => v
    row.setIfInBounds c v) (Array.replicate (n + 1) .null)

/-- The frame with candidate `j` of a FROM item bound into its slots. -/
def bindCand (src : CSource) (need : Array Bool) (frame : Row) (raw : Array (Int64 × ByteArray)) (cands : Array Row)
    (j : Nat) : Row :=
  let (base, tbl) := match src with
    | .table _ tn ipk rc dv base _ _ _ _ _ => (base, some (tn, ipk, rc, dv))
    | .sub _ _ base _ _ _ _ | .cte _ _ base _ _ _ _ | .tvf _ _ _ base _ _ _ => (base, none)
  match tbl, raw.isEmpty with
  | some (tn, ipk, rc, dv), false =>
    let (k, r) := raw.getD j (0, ByteArray.empty)
    fillRow frame base tn ipk rc dv need k r
  | _, _ =>
    let c := cands.getD j #[]
    c.size.fold (fun k _ (fr : Row) => fr.setIfInBounds (base + k) (c.getD k .null)) frame

/-- A table candidate's columns `rest` marks (none, when empty), once the row passed the conditions read from
`bindCand`'s columns. -/
def bindRest (src : CSource) (rest : Array Bool) (frame : Row) (raw : Array (Int64 × ByteArray)) (j : Nat) : Row :=
  match src, raw.isEmpty || rest.isEmpty with
  | .table _ tn ipk rc dv base _ _ _ _ _, false =>
    let (k, r) := raw.getD j (0, ByteArray.empty)
    fillRow frame base tn ipk rc dv rest k r
  | _, _ => frame

/-- A table item's row as a joined frame read it: its rowid and record (none for the other items, and for a LEFT JOIN's
row of NULLs). -/
abbrev RowRef := Option (Int64 × ByteArray)

/-- A sorted row's frame with its deferred columns (`late`) decoded from the table rows it was joined from. -/
def bindLate (srcs : Array CSource) (late : Array Bool) (frame : Row) (refs : Array RowRef) : Row :=
  srcs.size.fold (fun k _ fr => match srcs[k]?, refs[k]? with
    | some (.table _ n ipk rc dv base _ _ _ layout _), some (some (rid, rec_)) =>
      if layout.isEmpty then fillRow fr base n ipk rc dv late rid rec_ else fr
    | _, _ => fr) frame

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

/-- Moves entry `i` of a max-heap up while its parent is smaller. -/
def siftUp (cmp : α → α → Ordering) (h : Array α) (i : Nat) : Nat → Array α
  | 0 => h
  | f+1 =>
    if i == 0 then h else
    let p := (i - 1) / 2
    if hp : p < h.size ∧ i < h.size then
      if cmp h[p] h[i] == .lt then siftUp cmp (h.swap p i) p f else h
    else h

/-- Moves entry `i` of a max-heap down while a child is larger. -/
def siftDown (cmp : α → α → Ordering) (h : Array α) (i : Nat) : Nat → Array α
  | 0 => h
  | f+1 =>
    let l := 2 * i + 1
    let r := l + 1
    let big := if hl : l < h.size ∧ i < h.size then (if cmp h[i] h[l] == .lt then l else i) else i
    let big := if hr : r < h.size ∧ big < h.size then (if cmp h[big] h[r] == .lt then r else big) else big
    if hb : big ≠ i ∧ big < h.size ∧ i < h.size then siftDown cmp (h.swap i big) big f else h

/-- A max-heap of at most `n` entries offered `x`: kept while there is room, else in place of the largest entry when
smaller than it (the first `n` in order stay, as in sqlite's LIMIT sorter). -/
def heapOffer (cmp : α → α → Ordering) (n : Nat) (h : Array α) (x : α) : Array α :=
  if h.size < n then siftUp cmp (h.push x) h.size (h.size + 1)
  else match h[0]? with
    | some w => if cmp x w == .lt then siftDown cmp (h.setIfInBounds 0 x) 0 h.size else h
    | none => h

/-- Where ORDER BY's sorter reads a key: field `col` of FROM item `item`'s record, in place (`dflt` past the record's
end: a column added by ALTER TABLE), or the value of the key's expression. -/
inductive KeySrc where
  | field (item col : Nat) (dflt : Value)
  /-- FROM item `item`'s rowid (its INTEGER PRIMARY KEY) -/
  | rowid (item : Nat)
  /-- the value of the `j`th key that is neither -/
  | expr (j : Nat)
  deriving Inhabited

/-- A kept key record `a` against a candidate row's keys, read from its items' records (`refs`) or its key values
(`vals`), without decoding the fields. -/
def cmpKeyCand (dirs : Array (Bool × Bool × Collation)) (srcs : Array KeySrc) (refs : Array RowRef) (vals : Array Value)
    (a : ByteArray) : Ordering :=
  let (ha, ka) := getVarint a 0
  go ha.toNat ka ha.toNat 0 dirs.size
where
  go (ha pa oa i : Nat) : Nat → Ordering
    | 0 => .eq
    | f+1 =>
      if pa ≥ ha then .eq else
      let (ta, la) := getVarint a pa
      let (desc, nullsFirst, coll) := dirs.getD i (false, true, .binary)
      let value (v : Value) : Ordering :=
        keyOrder desc nullsFirst (serialClass ta == 0) v.isNull fun _ => cmpFieldValue coll a ta oa v
      let o := match srcs.getD i default with
        | .field item col dflt => match refs.getD item none with
          | some (_, r) => match recordField? r col with
            | some (t, o) => keyOrder desc nullsFirst (serialClass ta == 0) (serialClass t == 0) fun _ => cmpField coll a ta oa r t o
            | none => value dflt
          | none => value .null
        | .rowid item => value (match refs.getD item none with | some (k, _) => .int k | none => .null)
        | .expr j => value (vals.getD j .null)
      if o != .eq then o else go ha (pa + la) (oa + serialLen ta) (i+1) f

/-- A candidate row's key `i`: a record's field (serial type and body offset), or a value. -/
inductive KeyPart where
  | field (r : ByteArray) (t : UInt64) (o : Nat)
  | value (v : Value)

/-- The sort record of a candidate row's keys: record fields copied as they are, key values encoded. -/
def keyRecord (srcs : Array KeySrc) (refs : Array RowRef) (vals : Array Value) : ByteArray :=
  let parts := srcs.mapIdx fun i s => match s with
    | .field item col dflt => match refs.getD item none with
      | some (_, r) => match recordField? r col with
        | some (t, o) => KeyPart.field r t o
        | none => .value dflt
      | none => .value .null
    | .rowid item => .value (match refs.getD item none with | some (k, _) => .int k | none => .null)
    | .expr j => .value (vals.getD j .null)
  let types := parts.map fun p => match p with
    | .field _ t _ => (t, serialLen t)
    | .value v => serialType v
  parts.foldl (fun b p => match p with
    | .field r t o => r.copySlice o b b.size (serialLen t) false
    | .value v => pushBody b v) (recordHeader types)

/-- A row in ORDER BY's sorter: its keys packed in a record, its arrival (the last key, so equal keys keep it), its
computed result columns, and its frame with the table rows it was joined from (the deferred columns are decoded from
them once it is output). -/
structure SortEntry where
  key : ByteArray
  seq : Nat
  vals : Row
  frame : Row := #[]
  refs : Array RowRef := #[]
deriving Inhabited

def cmpEntry (dirs : Array (Bool × Bool × Collation)) (a b : SortEntry) : Ordering :=
  match cmpSortRecords dirs a.key b.key with
  | .eq => compare a.seq b.seq
  | o => o

/-- ORDER BY's sorter: a max-heap of the first `n` entries when bounded, else every entry. -/
structure Sorter where
  rows : Array SortEntry := #[]
  seq : Nat := 0

/-- Result rows in ORDER BY's order of their keys (packed into records), only the first `n` when bounded. -/
def orderRows (dirs : Array (Bool × Bool × Collation)) (bound : Option Nat) (rows : Array (Row × Row)) : Array (Row × Row) :=
  let es := rows.mapIdx fun i (vs, ks) => ({ key := encodeRecord ks, seq := i, vals := vs } : SortEntry)
  let es := match bound with
    | some n => es.foldl (heapOffer (cmpEntry dirs) n) #[]
    | none => es
  (sortBy es (cmpEntry dirs)).map fun e => (e.vals, #[])

/-- The rows whose result columns (compared field by field under `dirs`) no earlier row has, in order (DISTINCT): an
ordered set of the result rows seen keeps the first occurrences. -/
def firstRows (dirs : Array Collation) (rows : Array (Row × Row)) : Array (Row × Row) :=
  (rows.foldl (fun ((out : Array (Row × Row)), (seen : Std.TreeSet Row (cmpRowsColl dirs))) r =>
    let (dup, seen) := seen.containsThenInsert r.1
    (if dup then out else out.push r, seen)) (#[], {})).1

/-- The indexes of each row's first occurrence, in order (UNION, a recursive WITH table, window DISTINCT). -/
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

/-- The rows of a rowid range `[lo, hi]` whose records `keep` accepts. -/
def scanRange (p : Pager) (root : Pgno) (lo : Option Int64) (hi : Option Int64) (keep : ByteArray → Bool) :
    Array (Int64 × ByteArray) :=
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
        else go (c.next p) (if keep r then acc.push (k, r) else acc) f

/-- The rowids of index entries from the key `probe` on, while their first fields equal `eqv` and (when given) the
field after them stays within `hi`. -/
def scanIndex (p : Pager) (root : Pgno) (ki : KeyInfo) (probe eqv : Array Value) (hi : Option (Value × Bool)) :
    Array Int64 :=
  go (BTree.Cursor.seekKey p ki root probe) #[] (BTree.entryBound p)
where
  go (c : BTree.Cursor) (acc : Array Int64) : Nat → Array Int64
    | 0 => acc
    | f+1 =>
      match c.key p with
      | none => acc
      | some k =>
        if !eqv.isEmpty && cmpRecordProbe ki k eqv != .eq then acc else
        let past : Bool := match hi with
          | some (h, incl) =>
            let v := recordColumn k eqv.size
            if v.isNull then false else
            let o := cmpValues (ki.colls.getD eqv.size .binary) v h
            o == .gt || (!incl && o == .eq)
          | none => false
        if past then acc else
        let rid := match recordLast k with | .int r => r | _ => 0
        go (c.next p) (acc.push rid) f

/-- A transient index on a FROM item: its rows as read whole (a table's (rowid, record) pairs, or a subquery's or WITH
table's rows), and the positions of those whose key values are all non-NULL, sorted by key (equal keys in read order). -/
structure AutoIdx where
  raw : Array (Int64 × ByteArray)
  rows : Array Row
  keys : Array (Array Value × Nat)
  deriving Inhabited

/-- Key values in order, each under its collation. -/
def cmpAutoKey (colls : Array Collation) (a b : Array Value) : Ordering :=
  go 0 a.size
where
  go (k : Nat) : Nat → Ordering
    | 0 => .eq
    | f+1 => match cmpValues (colls.getD k .binary) (a.getD k .null) (b.getD k .null) with
      | .eq => go (k+1) f
      | o => o

/-- The keys of a FROM item's transient index (empty: it has none). -/
def CSource.autoKeys : CSource → Array (Nat × CExpr × Aff × Collation)
  | .table _ _ _ _ _ _ (.auto keys) _ _ _ _ | .sub _ _ _ _ _ _ keys | .cte _ _ _ _ _ _ keys => keys
  | _ => #[]

/-- The transient index on the columns at slots `keys` of a FROM item's rows (sqlite's automatic index): each key
value after the comparison's affinity, as the item's rows bound into a frame of `width` slots give it. -/
def buildAuto (src : CSource) (width : Nat) (keys : Array (Nat × CExpr × Aff × Collation)) (raw : Array (Int64 × ByteArray))
    (rows : Array Row) : AutoIdx :=
  let need := keys.foldl (fun m (s, _) => m.setIfInBounds s true) (Array.replicate width false)
  let frame : Row := Array.replicate width .null
  let count := if raw.isEmpty then rows.size else raw.size
  let entries := count.fold (fun j _ (acc : Array (Array Value × Nat)) =>
    let fr := bindCand src need frame raw rows j
    let key := keys.map fun (s, _, aff, _) => Value.applyCmpAff aff (fr.getD s .null)
    if key.any (·.isNull) then acc else acc.push (key, j)) #[]
  let colls := keys.map (·.2.2.2)
  { raw, rows, keys := sortBy entries fun a b => cmpAutoKey colls a.1 b.1 }

/-- The rows of a transient index whose key equals `probe`, in index order. -/
def autoSeek (ai : AutoIdx) (colls : Array Collation) (probe : Array Value) : Array (Int64 × ByteArray) × Array Row :=
  let idx := ai.keys
  let start := lower idx 0 idx.size (idx.size + 1)
  let js := collect idx start #[] (idx.size - start)
  if ai.raw.isEmpty then (#[], js.map (ai.rows.getD · #[])) else (js.map (ai.raw.getD · (0, ByteArray.empty)), #[])
where
  /-- the first entry in `[lo, hi)` not below the probe -/
  lower (idx : Array (Array Value × Nat)) (lo hi : Nat) : Nat → Nat
    | 0 => lo
    | f+1 =>
      if lo < hi then
        let mid := (lo + hi) / 2
        if cmpAutoKey colls ((idx.getD mid default).1) probe == .lt then lower idx (mid + 1) hi f else lower idx lo mid f
      else lo
  collect (idx : Array (Array Value × Nat)) (i : Nat) (acc : Array Nat) : Nat → Array Nat
    | 0 => acc
    | f+1 =>
      match idx[i]? with
      | some (key, j) => if cmpAutoKey colls key probe == .eq then collect idx (i + 1) (acc.push j) f else acc
      | none => acc

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

/-- The orderings a comparison operator accepts: `a op b` holds when `cmpValues a b` is one of them. -/
structure OrdSet where
  lt : Bool
  eq : Bool
  gt : Bool

def OrdSet.of : BinOp → OrdSet
  | .eq => ⟨false, true, false⟩
  | .ne => ⟨true, false, true⟩
  | .lt => ⟨true, false, false⟩
  | .le => ⟨true, true, false⟩
  | .gt => ⟨false, false, true⟩
  | .ge => ⟨false, true, true⟩
  | _ => ⟨false, false, false⟩

def OrdSet.has (s : OrdSet) : Ordering → Bool
  | .lt => s.lt
  | .eq => s.eq
  | .gt => s.gt

/-- A comparison's truth on operands the comparison affinity was applied to (NULL when either is). -/
def cmpTruth (s : OrdSet) (coll : Collation) (x y : Value) : Option Bool :=
  if x.isNull || y.isNull then none else some (s.has (cmpValues coll x y))

/-- Whether a comparison holds on operands the comparison affinity was applied to (not when either is NULL). -/
def cmpHolds (s : OrdSet) (coll : Collation) (x y : Value) : Bool :=
  !x.isNull && !y.isNull && s.has (cmpValues coll x y)

/-- The orderings the operator accepts with its operands swapped. -/
def OrdSet.swap (s : OrdSet) : OrdSet := ⟨s.gt, s.eq, s.lt⟩

/-- A condition on a table's column against a literal, decided on the record's bytes: the column's index, the orderings
the operator accepts (for the column against the literal), the collation, the comparison affinity, the literal with it
applied, whether the column's integers are reals, and the column's value in a record too short to have it. -/
structure LitCond where
  col : Nat
  ords : OrdSet
  coll : Collation
  aff : Aff
  lit : Value
  real : Bool
  dflt : Value

/-- Whether the condition holds for the field of serial type `t` whose body starts at `o`: decided on the bytes when
the affinity leaves the field's value as it is, else on the decoded field. -/
def LitCond.holds (c : LitCond) (rec_ : ByteArray) (t : UInt64) (o : Nat) : Bool :=
  let cls := serialClass t
  if cls == 0 || c.lit.isNull then false else
  let plain := !(c.real && cls == 1 && t != 7) && match c.aff with
    | .none | .blob => true
    | .numeric | .integer => cls != 2
    | .real => cls == 3 || t == 7
    | .text => cls != 1
  if plain then c.ords.has (cmpFieldValue c.coll rec_ t o c.lit)
  else
    let v := match decodeField rec_ o t with
      | .int x => if c.real then .real x.toFloat else .int x
      | v => v
    cmpHolds c.ords c.coll (Value.applyCmpAff c.aff v) c.lit

/-- Whether a record passes every condition (`lits` in column order): its header read once, the fields compared in place. -/
def litsPass (lits : Array LitCond) (rec_ : ByteArray) : Bool :=
  let (hs, p0) := getVarint rec_ 0
  go hs.toNat p0 hs.toNat 0 0 (lits.size + (lits.back?.map (·.col)).getD 0 + 1)
where
  go (hs pos body i j : Nat) : Nat → Bool
    | 0 => true
    | f+1 =>
      match lits[j]? with
      | none => true
      | some c =>
        if pos ≥ hs then
          cmpHolds c.ords c.coll (Value.applyCmpAff c.aff c.dflt) c.lit && go hs pos body i (j+1) f
        else
        let (t, l) := getVarint rec_ pos
        if i < c.col then go hs (pos + l) (body + serialLen t) (i+1) j f
        else c.holds rec_ t body && go hs pos body i (j+1) f

/-- AND and OR of truth values. -/
def andTruth : Option Bool → Option Bool → Option Bool
  | _, some false | some false, _ => some false
  | some true, some true => some true
  | _, _ => none

def orTruth : Option Bool → Option Bool → Option Bool
  | _, some true | some true, _ => some true
  | some false, some false => some false
  | _, _ => none

/-- A binary operator other than a comparison, AND or OR. -/
def arithV (op : BinOp) (x y : Value) : Value :=
  match op with
  | .concat => concatV x y
  | .bitAnd | .bitOr | .shl | .shr => bitop op x y
  | _ => arith op x y

def bitNotV (v : Value) : Value := match intOf v with | some i => .int (~~~i) | none => .null

/-- Whether `v` equals one of the values in `vs` (true), none does but one is NULL (none), or none does (false). -/
def inValues (aff : Aff) (coll : Collation) (v : Value) (vs : Array Value) : Option Bool :=
  let (found, sawNull) := vs.foldl (fun (acc : Bool × Bool) w =>
    if acc.1 then acc else if w.isNull then (false, true) else (isTrueV (compareV .eq aff coll v w), acc.2)) (false, false)
  if found then some true else if sawNull then none else some false

/-- Operator subtrees whose operands are all literals, replaced by their value (functions, aggregates, windows,
subqueries and RAISE are left as they are). -/
def foldConst : CExpr → Nat → CExpr
  | e, 0 => e
  | e, fuel+1 => match e with
  | .arith op a b => match foldConst a fuel, foldConst b fuel with
    | .lit x, .lit y => .lit (arithV op x y)
    | a, b => .arith op a b
  | .cmp op a b aff coll => match foldConst a fuel, foldConst b fuel with
    | .lit x, .lit y => .lit (compareV op aff coll x y)
    | a, b => .cmp op a b aff coll
  | .and a b => match foldConst a fuel, foldConst b fuel with
    | .lit x, .lit y => .lit (optBool (andTruth x.truth? y.truth?))
    | a, b => .and a b
  | .or a b => match foldConst a fuel, foldConst b fuel with
    | .lit x, .lit y => .lit (optBool (orTruth x.truth? y.truth?))
    | a, b => .or a b
  | .not a => match foldConst a fuel with
    | .lit x => .lit (optBool (x.truth?.map (!·)))
    | a => .not a
  | .neg a => match foldConst a fuel with
    | .lit x => .lit (negV x)
    | a => .neg a
  | .bitNot a => match foldConst a fuel with
    | .lit x => .lit (bitNotV x)
    | a => .bitNot a
  | .cast a aff => match foldConst a fuel with
    | .lit x => .lit (castV aff x)
    | a => .cast a aff
  | .isNull a neg => match foldConst a fuel with
    | .lit x => .lit (boolV (x.isNull != neg))
    | a => .isNull a neg
  | .fn name args => .fn name (args.map (foldConst · fuel))
  | .case base whens els aff coll =>
    .case (base.map (foldConst · fuel)) (whens.map fun (w, t) => (foldConst w fuel, foldConst t fuel)) (els.map (foldConst · fuel)) aff coll
  | .inList x items neg aff coll => .inList (foldConst x fuel) (items.map (foldConst · fuel)) neg aff coll
  | .inVals x vals hasNull neg aff coll => .inVals (foldConst x fuel) vals hasNull neg aff coll
  | .inSel x q neg aff coll corr => .inSel (foldConst x fuel) q neg aff coll corr
  | .matchE op x p esc neg => .matchE op (foldConst x fuel) (foldConst p fuel) (esc.map (foldConst · fuel)) neg
  | .inSelRow es q neg affs colls => .inSelRow (es.map (foldConst · fuel)) q neg affs colls
  | e => e

mutual
/-- An expression compiled to a closure. -/
def compileE (sub : SubRun) : CExpr → Nat → CFn
  | _, 0 => fun _ => .error "expression nested too deeply"
  | e, fuel+1 => match e with
  | .lit v => fun _ => .ok v
  | .col d s => fun env => .ok (env.col d s)
  | .arith op a b =>
    let fa := compileE sub a fuel
    let fb := compileE sub b fuel
    fun env => do
      let x ← fa env
      let y ← fb env
      return arithV op x y
  | .cmp .. | .and .. | .or .. | .not .. =>
    let t := compileT sub e fuel
    fun env => do return optBool (← t env)
  | .neg a =>
    let fa := compileE sub a fuel
    fun env => do return negV (← fa env)
  | .bitNot a =>
    let fa := compileE sub a fuel
    fun env => do return bitNotV (← fa env)
  | .fn name args =>
    if Json.isJsonFn name then
      let j := compileJ sub e fuel
      fun env => do return (← j env).1
    else
      let f := fnOf name
      let fs := args.map (compileE sub · fuel)
      fun env => do f env (← fs.mapM (· env))
  | .agg i => fun env => .ok (env.aggs.getD i .null)
  | .case base whens els aff coll =>
    let fb := base.map (compileE sub · fuel)
    let ws := whens.map fun (w, t) => (compileE sub w fuel, compileE sub t fuel)
    let fe := els.map (compileE sub · fuel)
    fun env => do
      let b ← match fb with
        | some f => do let v ← f env; pure (some v)
        | none => pure none
      for (w, t) in ws do
        let wv ← w env
        let hit : Bool := match b with
          | some b => isTrueV (compareV .eq aff coll b wv)
          | none => wv.truth? == some true
        if hit then return (← t env)
      match fe with
      | some f => f env
      | none => return .null
  | .cast x aff =>
    let fa := compileE sub x fuel
    fun env => do return castV aff (← fa env)
  | .inList x items neg aff coll =>
    if items.isEmpty then fun _ => .ok (boolV neg) else
    let fx := compileE sub x fuel
    let fs := items.map (compileE sub · fuel)
    fun env => do
      let v ← fx env
      if v.isNull then return .null
      let mut sawNull := false
      let mut found := false
      for f in fs do
        let w ← f env
        if w.isNull then sawNull := true
        else if isTrueV (compareV .eq aff coll v w) then found := true; break
      return if found then boolV (!neg) else if sawNull then .null else boolV neg
  | .inVals x vals hasNull neg aff coll =>
    let fx := compileE sub x fuel
    fun env => do
      let v ← fx env
      if v.isNull then return .null
      if memSorted coll vals (Value.applyCmpAff aff v) then return boolV (!neg)
      return if hasNull then .null else boolV neg
  | .inSel x q neg aff coll _ =>
    let fx := compileE sub x fuel
    fun env => do
      let v ← fx env
      if v.isNull then return .null
      let rows ← sub env q
      return match inValues aff coll v (rows.map (·.getD 0 .null)) with
        | some true => boolV (!neg)
        | none => .null
        | some false => boolV neg
  | .exists q neg _ => fun env => do return boolV ((← sub env q).isEmpty == neg)
  | .scalar q _ => fun env => do
    let rows ← sub env q
    return ((rows[0]?).bind (·[0]?)).getD .null
  | .matchE op x pat esc neg =>
    let fx := compileE sub x fuel
    let generic : CFn :=
      let fp := compileE sub pat fuel
      let fe := esc.map (compileE sub · fuel)
      fun env => do
        let v ← fx env
        let pv ← fp env
        let ev ← match fe with
          | some f => do let r ← f env; pure (some r)
          | none => pure none
        if v.isNull || pv.isNull then return .null
        if let some ev := ev then if ev.isNull then return .null
        let escB ← match ev with
          | some ev =>
            match likeEscape ev.toBytes with
            | some e => pure (some e)
            | none => throw "ESCAPE expression must be a single character"
          | none => pure none
        let m := match op with
          | .glob => globMatch pv.toBytes v.toBytes
          | _ => likeMatch pv.toBytes v.toBytes escB
        return boolV (m != neg)
    -- a constant pattern (and escape): their bytes taken once, not per row
    let withLit (pat : ByteArray) (esc : Option ByteArray) : CFn := fun env => do
      let v ← fx env
      if v.isNull then return .null
      let m := match op with
        | .glob => globMatch pat v.toBytes
        | _ => likeMatch pat v.toBytes esc
      return boolV (m != neg)
    match pat, esc with
    | .lit pv, none => if pv.isNull then generic else withLit pv.toBytes none
    | .lit pv, some (.lit ev) =>
      match likeEscape ev.toBytes with
      | some e => if pv.isNull || ev.isNull then generic else withLit pv.toBytes (some e)
      | none => generic
    | _, _ => generic
  | .isNull x neg =>
    let fa := compileE sub x fuel
    fun env => do return boolV ((← fa env).isNull != neg)
  | .inSelRow es q neg affs colls =>
    let fs := es.map (compileE sub · fuel)
    fun env => do
      let vs ← fs.mapM (· env)
      let rows ← sub env q
      let mut sawNull := false
      let mut found := false
      for r in rows do
        let cs := vs.mapIdx fun i v => compareV .eq (affs.getD i .none) (colls.getD i .binary) v (r.getD i .null)
        if cs.all isTrueV then found := true; break
        -- no pair differs, but one is NULL: unknown
        if !cs.any (fun c => c.truth? == some false) && cs.any (·.isNull) then sawNull := true
      return if found then boolV (!neg) else if sawNull then .null else boolV neg
  | .win i => fun env => .ok (env.wins.getD i .null)
  | .raise k m => fun _ => .error (raiseMsg k m)

/-- An expression's truth value, compiled. -/
def compileT (sub : SubRun) : CExpr → Nat → CTruth
  | _, 0 => fun _ => .error "expression nested too deeply"
  | e, fuel+1 => match e with
  | .and a b =>
    let ta := compileT sub a fuel
    let tb := compileT sub b fuel
    fun env => do
      let x ← ta env
      if x == some false then return some false
      return andTruth x (← tb env)
  | .or a b =>
    let ta := compileT sub a fuel
    let tb := compileT sub b fuel
    fun env => do
      let x ← ta env
      if x == some true then return some true
      return orTruth x (← tb env)
  | .not a =>
    let ta := compileT sub a fuel
    fun env => do return (← ta env).map (!·)
  | .cmp op a b aff coll =>
    let fa := compileE sub a fuel
    let fb := compileE sub b fuel
    match op with
    | .is | .isNot => fun env => do
      let x ← fa env
      let y ← fb env
      return (compareV op aff coll x y).truth?
    | _ =>
      -- both operands with the comparison affinity, a literal's applied once
      let t := cmpTruth (OrdSet.of op) coll
      match a, b with
      | _, .lit w =>
        let w := Value.applyCmpAff aff w
        fun env => do return t (Value.applyCmpAff aff (← fa env)) w
      | .lit w, _ =>
        let w := Value.applyCmpAff aff w
        fun env => do return t w (Value.applyCmpAff aff (← fb env))
      | _, _ => fun env => do
        let x ← fa env
        let y ← fb env
        return t (Value.applyCmpAff aff x) (Value.applyCmpAff aff y)
  | e =>
    let f := compileE sub e fuel
    fun env => do return (← f env).truth?

/-- An expression compiled to its value and whether that carries sqlite's JSON subtype (the direct result of a JSON
function or aggregate). -/
def compileJ (sub : SubRun) : CExpr → Nat → CFnJ
  | _, 0 => fun _ => .error "expression nested too deeply"
  | e, fuel+1 => match e with
  | .fn name args =>
    if Json.isJsonFn name then
      let fs := args.map (compileJ sub · fuel)
      fun env => do
        let vs ← fs.mapM (· env)
        Json.callJ name (vs.map (·.1)) (vs.map (·.2))
    else if name == jsonValueTag then
      let fv := compileE sub (args.getD 0 (.lit .null)) fuel
      let ft := compileE sub (args.getD 1 (.lit .null)) fuel
      fun env => do
        let v ← fv env
        let t ← ft env
        return (v, t == .text "array" || t == .text "object")
    else
      let f := compileE sub e fuel
      fun env => do return (← f env, false)
  | .agg i => fun env => .ok (env.aggs.getD i .null, env.aggJson.getD i false)
  | e =>
    let f := compileE sub e fuel
    fun env => do return (← f env, false)
end

/-- A WHERE or ON condition compiled: whether it is true (an AND is true when both sides are). -/
def compileW (sub : SubRun) : CExpr → Nat → CPred
  | _, 0 => fun _ => .error "expression nested too deeply"
  | e, fuel+1 => match e with
  | .and a b =>
    let wa := compileW sub a fuel
    let wb := compileW sub b fuel
    fun env => do if !(← wa env) then return false else wb env
  | e =>
    let t := compileT sub e fuel
    fun env => do return (← t env) == some true

namespace CExpr
/-- The expression's value, compiled (operators over literals folded first). -/
def compile (sub : SubRun) (e : CExpr) (fuel : Nat) : CFn := compileE sub (foldConst e fuel) fuel
/-- Whether the expression is true, compiled. -/
def compileTrue (sub : SubRun) (e : CExpr) (fuel : Nat) : CPred :=
  let t := compileT sub (foldConst e fuel) fuel
  fun env => do return (← t env) == some true
/-- A WHERE or ON condition, compiled. -/
def compileCond (sub : SubRun) (e : CExpr) (fuel : Nat) : CPred := compileW sub (foldConst e fuel) fuel
/-- The expression's value and JSON subtype, compiled. -/
def compileJson (sub : SubRun) (e : CExpr) (fuel : Nat) : CFnJ := compileJ sub (foldConst e fuel) fuel
end CExpr

/-- Conditions compiled to one: whether every one is true (checked in order, up to the first that is not). -/
def compileConds (sub : SubRun) (conds : Array CExpr) (fuel : Nat) : CPred :=
  let ps := conds.map (·.compileCond sub fuel)
  fun env => ps.allM (· env)

/-- A condition's conjuncts, in order. -/
def CExpr.conjuncts : CExpr → Nat → Array CExpr
  | .and a b, f+1 => a.conjuncts f ++ b.conjuncts f
  | e, _ => #[e]

/-- `column op literal` (either way round) on a table's columns (not its rowid), as a `LitCond`. -/
def litCondOf (base n : Nat) (ipk : Option Nat) (rc : Array Bool) (dv : Array Value) : CExpr → Option LitCond
  | .cmp op (.col 0 s) (.lit w) aff coll => mk op s w aff coll false
  | .cmp op (.lit w) (.col 0 s) aff coll => mk op s w aff coll true
  | _ => none
where
  mk (op : BinOp) (s : Nat) (w : Value) (aff : Aff) (coll : Collation) (flip : Bool) : Option LitCond :=
    let ord := op == .eq || op == .ne || op == .lt || op == .le || op == .gt || op == .ge
    if ord && base ≤ s && s < base + n && ipk != some (s - base) then
      let k := s - base
      let ords := OrdSet.of op
      some { col := k, ords := if flip then ords.swap else ords, coll, aff, lit := Value.applyCmpAff aff w,
             real := rc.getD k false, dflt := dv.getD k .null }
    else none

/-- A table scan's conditions split: the leading conjuncts that compare a column to a literal (in column order), and the
conditions after them (a later condition may fail on a row an earlier one rejects, so only a prefix moves ahead). -/
def litSplit (fuel : Nat) (s : CSource) (conds : Array CExpr) : Array LitCond × Array CExpr :=
  match s with
  | .table _ n ipk rc dv base access false false layout _ =>
    if !access.isScan || !layout.isEmpty then (#[], conds) else
    let cs := conds.foldl (fun acc c => acc ++ (foldConst c fuel).conjuncts 64) #[]
    let k := (cs.findIdx? fun c => (litCondOf base n ipk rc dv c).isNone).getD cs.size
    let lits := (cs.extract 0 k).filterMap (litCondOf base n ipk rc dv)
    if lits.isEmpty then (#[], conds) else (sortBy lits fun a b => compare a.col b.col, cs.extract k cs.size)
  | _ => (#[], conds)

/-- A FROM item's compiled closures: its ON conditions, its WHERE conditions, its access path's probes, its transient
index's probes (with their affinities), and a table-valued function's arguments. A table scan's leading conditions on a
column against a literal (`lits`) are decided on its records as the scan reads them; `resid` is the conditions that
remain to check once a row is bound. -/
structure SrcRun where
  on : CPred
  conds : CPred
  lits : Array LitCond
  resid : CPred
  access : Access CFn
  auto : Array (CFn × Aff)
  args : Array CFn

instance : Inhabited SrcRun :=
  let no : CPred := fun _ => .ok false
  ⟨⟨no, no, #[], no, .full, #[], #[]⟩⟩

/-- An aggregate's compiled closures: its arguments (with their JSON subtypes for a JSON aggregate), FILTER, and step;
`coll`: its argument's collation (min(), max() and DISTINCT compare under it). -/
structure AggRun where
  name : String
  json : Bool
  distinct : Bool
  args : Array CFn
  argsJ : Array CFnJ
  filter : Option CPred
  step : AggStepFn
  coll : Collation

/-- Orders the arguments a group's DISTINCT aggregates have seen, (aggregate, its arguments): by aggregate, then under
that aggregate's collations in `dd` (its argument's). -/
def cmpSeen (dd : Array (Array Collation)) (a b : Nat × Row) : Ordering :=
  match compare a.1 b.1 with
  | .eq => cmpRowsColl (dd.getD a.1 #[]) a.2 b.2
  | o => o

/-- A group of an aggregate query (with no GROUP BY, the one group), stepped as its rows arrive: each aggregate's
accumulator, its row count, the frame its bare columns read, whether its last row loaded that frame (sqlite's regHit),
and the arguments its DISTINCT aggregates have seen. -/
structure Group (dd : Array (Array Collation)) where
  accs : Array AggAcc
  n : Nat := 0
  frame : Row
  hit : Bool := false
  seen : Std.TreeSet (Nat × Row) (cmpSeen dd) := {}

/-- A row into its group: `ins`, each aggregate's arguments and (a JSON aggregate's) which are JSON (none: its FILTER
rejects the row). As sqlite's accumulator load, the bare columns read the group's first row, then each row at which the
last min() or max() to see it takes a new best value (or a NULL while it has none); a row its FILTER rejects loads
nothing, and a DISTINCT duplicate leaves the decision as the row before made it. -/
def Group.step (aggs : Array AggRun) (g : Group dd) (ins : Array (Option (Array Value × Array Bool))) (frame : Row) :
    Group dd :=
  let n := g.n
  let (accs, seen, hit) := aggs.size.fold (fun j h (accs, seen, hit) =>
    let a := aggs[j]
    let mm := a.name == "MIN" || a.name == "MAX"
    match ins.getD j none with
    | none => (accs, seen, hit && !mm)
    | some (vs, js) =>
      let (dup, seen) := if a.distinct then seen.containsThenInsert (j, vs) else (false, seen)
      if dup then (accs, seen, hit) else
      -- taken out of the array first, so it is updated in place
      let acc := accs.getD j {}
      let had := acc.any
      let accs := accs.setIfInBounds j {}
      let acc := if a.json then { acc with json := Json.aggStep a.name acc.json vs js } else a.step acc vs n
      (accs.setIfInBounds j acc, seen, if mm then !had || acc.bestAt == n else hit)) (g.accs, g.seen, g.hit)
  { accs, n := n + 1, frame := if n == 0 || hit then frame else g.frame, hit, seen }

/-- A SELECT core's expressions, compiled. -/
structure CoreRun where
  pre : CPred
  runs : Array SrcRun
  groupBy : Array CFn
  aggs : Array AggRun
  having : Option CPred
  cols : Array CFn
  order : Array CFn
  /-- the frame slots some expression reads -/
  need : Array Bool
  /-- each FROM item's columns in two stages: those its ON and WHERE conditions read, then the rest of `need` -/
  needs : Array (Array Bool × Array Bool)
  /-- the slots only plain result columns read, of the table items read as records: a sorter decodes them only for the
  rows it outputs -/
  late : Array Bool
  /-- where a sorter reads each ORDER BY key -/
  keys : Array KeySrc
deriving Inhabited

/-- A core's expressions compiled once, for all its rows (a VALUES core has none). -/
def CCore.compile (sub : SubRun) (core : CCore) (fuel : Nat) : CoreRun :=
  match core with
  | .values .. => default
  | .select srcs pre filters groupBy _ having cols _ order aggs _ _ width wins =>
    let srcExprs := srcs.foldl (fun acc s => match s with
      | .table _ _ _ _ _ _ acc' _ _ _ on => acc ++ on ++ acc'.exprs
      | .sub _ _ _ _ _ on keys | .cte _ _ _ _ _ on keys => acc ++ on ++ keys.map (·.2.1)
      | .tvf _ args _ _ _ _ on => acc ++ args ++ on) #[]
    let aggArgs := aggs.foldl (fun acc (.mk _ _ _ args _ f) => acc ++ args ++ f.toArray) #[]
    let winExprs := wins.foldl (fun acc (.mk _ _ _ args f part _ ord _ _ s fi _) =>
      acc ++ args ++ f.toArray ++ part ++ ord ++ boundExprs s ++ boundExprs fi) #[]
    let readers (cs os : Array CExpr) (fs : Array (Array CExpr)) := neededSlots width (cs ++ os ++ groupBy ++ having.toArray
      ++ pre ++ fs.foldl (· ++ ·) #[] ++ srcExprs ++ aggArgs ++ winExprs)
    let needOf (fs : Array (Array CExpr)) := readers cols order fs
    let need := needOf filters
    -- what a sorter reads in place and decodes late (nothing to sort: none)
    let (keys, late) : Array KeySrc × Array Bool := if order.isEmpty then (#[], #[]) else
      -- a sorter reads a key that is a column of a table item read as records in place, from the record
      let fieldOf (s : Nat) : Option KeySrc := (srcs.mapIdx fun i src => (i, src)).findSome? fun (i, src) => match src with
        | .table _ n ipk _ dv base _ _ _ layout _ =>
          if !layout.isEmpty || s < base || s > base + n then none
          else if s == base + n || ipk == some (s - base) then some (.rowid i)
          else some (.field i (s - base) (dv.getD (s - base) .null))
        | _ => none
      -- each key read in place, or numbered among the keys evaluated
      let keys := (order.foldl (fun ((ks : Array KeySrc), j) o => match o with
        | .col 0 s => match fieldOf s with
          | some k => (ks.push k, j)
          | none => (ks.push (.expr j), j + 1)
        | _ => (ks.push (.expr j), j + 1)) (#[], 0)).1
      let isPlain (c : CExpr) : Bool := c matches .col 0 _
      let recSlots := srcs.foldl (fun m s => match s with
        | .table _ n _ _ _ base _ _ _ layout _ => if layout.isEmpty then (n + 1).fold (fun k _ m => m.setIfInBounds (base + k) true) m else m
        | _ => m) (Array.replicate width false)
      let others := readers (cols.filter (!isPlain ·)) ((order.zip keys).filterMap fun (o, k) => if k matches .expr _ then some o else none) filters
      let mark (m : Array Bool) (c : CExpr) : Array Bool := match c with | .col 0 s => m.setIfInBounds s true | _ => m
      let plainRead := order.foldl mark (cols.foldl mark (Array.replicate width false))
      let late := plainRead.mapIdx fun k b => b && recSlots.getD k false && !others.getD k false
      (keys, late)
    -- each scan's conditions on a column against a literal, decided as its records are read
    let splits := srcs.mapIdx fun i s => litSplit fuel s (filters.getD i #[])
    let needs := srcs.mapIdx fun i s =>
      let on := match s with
        | .table _ _ _ _ _ _ _ _ _ _ on | .sub _ _ _ _ _ on _ | .cte _ _ _ _ _ on _ | .tvf _ _ _ _ _ _ on => on
      let (lits, others) := splits.getD i (#[], #[])
      let conds := on ++ others
      -- (the columns only those conditions read are not bound at all)
      let need := if lits.isEmpty then need else needOf (filters.setIfInBounds i others)
      -- (only for a scan: a lookup's few rows are not worth it)
      match s with
      | .table _ _ _ _ _ _ access _ _ layout _ =>
        if conds.isEmpty || !layout.isEmpty || !access.isScan then (need, #[]) else
        let first := neededSlots width conds
        (first, need.mapIdx fun k b => b && !first.getD k false)
      | _ => (need, #[])
    let runs := srcs.mapIdx fun i s =>
      let (on, access, auto, args) := match s with
        | .table _ _ _ _ _ _ access _ _ _ on => (on, access, s.autoKeys, #[])
        | .sub _ _ _ _ _ on keys | .cte _ _ _ _ _ on keys => (on, .full, keys, #[])
        | .tvf _ args _ _ _ _ on => (on, .full, #[], args)
      let conds := compileConds sub (filters.getD i #[]) fuel
      let (lits, others) := splits.getD i (#[], #[])
      ({ on := compileConds sub on fuel, conds, lits, resid := if lits.isEmpty then conds else compileConds sub others fuel,
         access := access.map (·.compile sub fuel), auto := auto.map fun (_, x, aff, _) => (x.compile sub fuel, aff),
         args := args.map (·.compile sub fuel) } : SrcRun)
    let aggs := aggs.map fun (a : CAgg) => match a with
      | .mk name dist star args coll flt =>
        ({ name, json := Json.isJsonAgg name, distinct := dist, args := args.map (CExpr.compile sub · fuel),
           argsJ := args.map (CExpr.compileJson sub · fuel), filter := flt.map (CExpr.compileTrue sub · fuel),
           step := aggStepOf name star coll, coll } : AggRun)
    { pre := compileConds sub pre fuel, runs, groupBy := groupBy.map (·.compile sub fuel), aggs,
      having := having.map (·.compileTrue sub fuel), cols := cols.map (·.compile sub fuel),
      order := order.map (·.compile sub fuel), need, needs, late, keys }

/-- An ordered scan's rows not read yet: its next chunk (at most `n` rows) and what follows it (none: the scan is over). -/
structure Rest where
  next : Nat → Array (Int64 × ByteArray) × Option Rest

namespace Rest
def empty : Rest := ⟨fun _ => (#[], none)⟩

/-- Up to `n` rows from cursor `c` on. `read c`: none when the scan is over before `c`, some none for an entry to skip, else
its row; `step`: the next entry. The cursor after them, when the scan goes on. -/
def take (read : BTree.Cursor → Option (Option (Int64 × ByteArray))) (step : BTree.Cursor → BTree.Cursor) (n : Nat)
    (c : BTree.Cursor) (acc : Array (Int64 × ByteArray)) : Nat → Array (Int64 × ByteArray) × Option BTree.Cursor
  | 0 => (acc, none)
  | f+1 =>
    if acc.size ≥ n then (acc, some c) else
    match read c with
    | none => (acc, none)
    | some none => take read step n (step c) acc f
    | some (some r) => take read step n (step c) (acc.push r) f

/-- A cursor scan read in chunks (`b`: an upper bound on the entries and chunks). -/
def scan (read : BTree.Cursor → Option (Option (Int64 × ByteArray))) (step : BTree.Cursor → BTree.Cursor) (c : BTree.Cursor) :
    Nat → Rest
  | 0 => empty
  | b+1 => ⟨fun n =>
    let (rows, c') := take read step n c #[] b
    (rows, c'.map fun c' => scan read step c' b)⟩
end Rest

/-- A table's rows from rowid `lo` to `hi` that pass `keep`, in rowid order or backwards. -/
def tableRest (p : Pager) (root : Pgno) (lo hi : Option Int64) (desc : Bool) (keep : ByteArray → Bool) : Rest :=
  let c := if desc then (match hi with | some h => BTree.Cursor.seekRowidLE p root h | none => BTree.Cursor.last p root)
    else (match lo with | some l => BTree.Cursor.seekRowid p root l | none => BTree.Cursor.first p root)
  let read (c : BTree.Cursor) : Option (Option (Int64 × ByteArray)) :=
    match c.row p with
    | none => none
    | some (k, r) =>
      if (if desc then lo.any (k < ·) else hi.any (k > ·)) then none else some (if keep r then some (k, r) else none)
  Rest.scan read (if desc then BTree.Cursor.prev p else BTree.Cursor.next p) c (BTree.entryBound p)

/-- An index access's probe values: its equality values (none when one is NULL), then its lower and upper bounds. -/
def indexProbes (e : Env) (eqs : Array (CFn × Aff)) (lo : Option (CFn × Bool × Aff)) (hi : Option (CFn × Bool × Aff)) :
    EM (Option (Array Value × Option Value × Option (Value × Bool))) := do
  let mut eqv : Array Value := #[]
  for (x, aff) in eqs do
    let v := Value.applyCmpAff aff (← x e)
    if v.isNull then return none
    eqv := eqv.push v
  let lov ← match lo with
    | some (x, _, aff) =>
      do
        let v := Value.applyCmpAff aff (← x e)
        pure (if v.isNull then none else some v)
    | none => pure none
  let hiv ← match hi with
    | some (x, incl, aff) =>
      do
        let v := Value.applyCmpAff aff (← x e)
        pure (if v.isNull then none else some (v, incl))
    | none => pure none
  return some (eqv, lov, hiv)

/-- The rows of an index's range, found in the table, in index order or backwards (equal keys then by rowid, descending). -/
def indexRest (p : Pager) (root iroot : Pgno) (ki : KeyInfo) (eqv : Array Value) (lov : Option Value)
    (hiv : Option (Value × Bool)) (desc : Bool) : Rest :=
  let neq := eqv.size
  let c := if !desc then
      -- with no lower bound, NULL entries (which sort first) are skipped by starting after them
      BTree.Cursor.seekKey p ki iroot (match lov, hiv with
        | some v, _ => eqv.push v
        | none, some _ => eqv.push (Value.real (-1.0/0.0))
        | none, none => eqv)
    else match hiv with
      | some (h, incl) =>
        -- (the entries equal to `h` are after the range unless it includes them)
        let hp := eqv.push h
        BTree.Cursor.before p iroot (if incl then BTree.Cursor.seekKeyAfter p ki iroot hp else BTree.Cursor.seekKey p ki iroot hp)
      | none => if eqv.isEmpty then BTree.Cursor.last p iroot
        else BTree.Cursor.before p iroot (BTree.Cursor.seekKeyAfter p ki iroot eqv)
  let coll := ki.colls.getD neq .binary
  let read (c : BTree.Cursor) : Option (Option (Int64 × ByteArray)) :=
    match c.key p with
    | none => none
    | some k =>
      if neq > 0 && cmpRecordProbe ki k eqv != .eq then none else
      let v := if lov.isSome || hiv.isSome then recordColumn k neq else .null
      let past := match hiv with
        | some (h, incl) => !v.isNull && (let o := cmpValues coll v h; o == .gt || (!incl && o == .eq))
        | none => false
      let below := match lov with
        | some l => v.isNull || cmpValues coll v l == .lt
        | none => hiv.isSome && v.isNull
      if past || below then none else
      let rid := match recordLast k with | .int r => r | _ => 0
      some ((BTree.tableFind p root rid).map fun cell => (rid, cell.payload))
  Rest.scan read (if desc then BTree.Cursor.prev p else BTree.Cursor.next p) c (BTree.entryBound p)

/-- The rows a FROM item offers for the current frame: a table's (rowid, record) pairs through its access path, or a
subquery's or WITH table's rows. `auto`: the item's transient index. -/
def candidatesAll (e : Env) (src : CSource) (run : SrcRun) (sub : Option (Array Row)) (auto : Option (Thunk AutoIdx)) :
    Nat → EM (Array (Int64 × ByteArray) × Array Row)
  | 0 => .error "query nested too deeply"
  | _+1 => do
    if let some ai := auto then
      let keys := src.autoKeys
      let mut probe : Array Value := #[]
      for (x, aff) in run.auto do
        let v := Value.applyCmpAff aff (← x e)
        if v.isNull then return (#[], #[])
        probe := probe.push v
      return autoSeek ai.get (keys.map (·.2.2.2)) probe
    match src with
    | .sub .. => .ok (#[], sub.getD #[])
    | .cte id .. => .ok (#[], e.ctes.getD id #[])
    | .tvf fn _ _ _ _ _ _ => do
      let vs ← run.args.mapM (· e)
      if fn.startsWith "pragma_" then
        return (#[], ((schemaPragma e.schema (fn.drop 7).toString ((vs.getD 0 .null).toText)).map (·.2)).getD #[])
      let rows ← tvfRows (fn == "json_tree") (vs.getD 0 .null) vs[1]?
      return (#[], rows)
    | .table root n _ realCols defaults _ _ _ _ layout _ => do
      let p := e.pager
      -- a WITHOUT ROWID table: its index-format tree's records, each field placed in its column
      if !layout.isEmpty then
        return (#[], BTree.foldIndex p root #[] fun acc r => acc.push (worRow n layout realCols defaults r))
      let dec (rs : Array (Int64 × ByteArray)) : Array (Int64 × ByteArray) × Array Row := (rs, #[])
      let find (k : Int64) : Array (Int64 × ByteArray) :=
        match BTree.tableFind p root k with | some c => #[(k, c.payload)] | none => #[]
      match run.access with
      | .full => return dec (BTree.foldTable p root #[] fun acc k r => if litsPass run.lits r then acc.push (k, r) else acc)
      | .rowidEq x => do
        let v ← x e
        return match toRowid? v with | some k => dec (find k) | none => (#[], #[])
      | .rowidIn items => do
        let vs ← items.mapM (· e)
        let ks := sortBy (vs.filterMap toRowid?) compare
        let ks := ks.foldl (fun acc k => if acc.back? == some k then acc else acc.push k) #[]
        return dec (ks.foldl (fun acc k => acc ++ find k) #[])
      | .rowidRange lo hi => do
        let lo' ← match lo with
          | some (x, incl) => do let v ← x e; pure (boundRowid v incl true)
          | none => pure none
        let hi' ← match hi with
          | some (x, incl) => do let v ← x e; pure (boundRowid v incl false)
          | none => pure none
        return dec (scanRange p root lo' hi' (litsPass run.lits))
      | .index iroot ki eqs lo hi => do
        let some (eqv, lov, hiv) ← indexProbes e eqs lo hi | return (#[], #[])
        -- with no lower bound, NULL entries (which sort first) are skipped by starting after them
        let probe := match lov with
          | some v => eqv.push v
          | none => if hiv.isSome then eqv.push (.real (-1.0/0.0)) else eqv
        let rids := scanIndex p iroot ki probe eqv hiv
        return dec (rids.foldl (fun acc k => acc ++ find k) #[])
      -- with no transient index passed in (a RIGHT JOIN's own pass), the whole table
      | .auto _ => return dec (BTree.foldTable p root #[] fun acc k r => acc.push (k, r))
      | .ordered _ _ => return dec (BTree.foldTable p root #[] fun acc k r => acc.push (k, r))

/-- A FROM item's candidate rows: those of `candidatesAll`, or (an ordered access path) a lazy scan of the table in order,
whose first chunk is still to be read (`Rest`). -/
def candidates (e : Env) (src : CSource) (run : SrcRun) (sub : Option (Array Row)) (auto : Option (Thunk AutoIdx)) :
    Nat → EM (Array (Int64 × ByteArray) × Array Row × Option Rest)
  | 0 => .error "query nested too deeply"
  | fuel+1 => do
    match run.access, src with
    | .ordered desc a, .table root .. =>
      let p := e.pager
      match a with
      | .full => return (#[], #[], some (tableRest p root none none desc (litsPass run.lits)))
      | .rowidRange lo hi =>
        let lo' ← match lo with
          | some (x, incl) => do let v ← x e; pure (boundRowid v incl true)
          | none => pure none
        let hi' ← match hi with
          | some (x, incl) => do let v ← x e; pure (boundRowid v incl false)
          | none => pure none
        return (#[], #[], some (tableRest p root lo' hi' desc (litsPass run.lits)))
      | .index iroot ki eqs lo hi =>
        match ← indexProbes e eqs lo hi with
        | some (eqv, lov, hiv) => return (#[], #[], some (indexRest p root iroot ki eqv lov hiv desc))
        | none => return (#[], #[], none)
      | a =>
        let (raw, cs) ← candidatesAll e src { run with access := a } sub auto fuel
        return (raw, cs, none)
    | _, _ =>
      let (raw, cs) ← candidatesAll e src run sub auto fuel
      return (raw, cs, none)

/-- The nested-loop join from FROM item `i` on: each candidate row of the item bound into the frame, its conditions
checked, then the later items; each joined frame goes to `emit` (with the items' `RowRef`s when `track`), until `stop`
holds; a LEFT JOIN's item with no match binds NULLs; a RIGHT JOIN's matched rows are marked. `needs`: each item's slots
its conditions read, and the rest it binds once they pass. -/
def joinFrom (emit : σ → Env → Array RowRef → EM σ) (stop : σ → Bool) (track : Bool) (e : Env) (srcs : Array CSource)
    (runs : Array SrcRun) (subs : Array (Option (Array Row))) (autos : Array (Option (Thunk AutoIdx)))
    (needs : Array (Array Bool × Array Bool)) (i : Nat) (refs : Array RowRef) (acc : σ × Array Bool) :
    Nat → EM (σ × Array Bool)
  | 0 => .error "query nested too deeply"
  | fuel+1 => do
    let some src := srcs[i]? | return (← emit acc.1 e refs, acc.2)
    let (base, n, left, right) := match src with
      | .table _ n _ _ _ base _ left right _ _ => (base, n + 1, left, right)
      | .sub _ n base left right _ _ => (base, n, left, right)
      | .cte _ n base left right _ _ => (base, n, left, right)
      | .tvf _ _ n base left right _ => (base, n, left, right)
    let run := runs.getD i default
    let (raw, cands, more) ← candidates e src run (subs.getD i none) (autos.getD i none) fuel
    let (first, rest) := needs.getD i (#[], #[])
    let mut acc := acc
    let mut matched := false
    -- an ordered scan's rows come in chunks, each larger than the last, only while `stop` has not held
    let mut raw := raw
    let mut more := more
    let mut want := 16
    for _ in [0:BTree.entryBound e.pager] do
      let count := if raw.isEmpty then cands.size else raw.size
      for j in [0:count] do
        if stop acc.1 then break
        let ej := e.modifyTop (bindCand src first · raw cands j)
        if left || right then
          unless ← run.on ej do continue
        matched := true
        if right then acc := (acc.1, acc.2.setIfInBounds j true)
        if ← run.resid ej then
          let ej := ej.modifyTop (bindRest src rest · raw j)
          acc ← joinFrom emit stop track ej srcs runs subs autos needs (i+1) (if track then refs.push raw[j]? else refs) acc fuel
      match more with
      | some r =>
        if stop acc.1 then break
        let (rows, next) := r.next want
        raw := rows
        more := next
        want := want * 4
      | none => break
    if left && !matched then
      let en := e.modifyTop fun fr => n.fold (fun k _ (fr : Row) => fr.setIfInBounds (base + k) .null) fr
      if ← run.conds en then
        acc ← joinFrom emit stop track en srcs runs subs autos needs (i+1) (if track then refs.push none else refs) acc fuel
    return acc

/-- A core's join into a consumer (`joinFrom` from the first item), then a RIGHT or FULL JOIN item's rows nothing
matched, with NULLs for the items before it. `rightIdx`: that item; `env`: the enclosing query's; `need`: the slots any
expression reads. -/
def joinAll (emit : σ → Env → Array RowRef → EM σ) (stop : σ → Bool) (track : Bool) (rightIdx : Option Nat)
    (env : Env) (frame0 : Row) (srcs : Array CSource) (runs : Array SrcRun) (subs : Array (Option (Array Row))) (autos : Array (Option (Thunk AutoIdx)))
    (needs : Array (Array Bool × Array Bool)) (need : Array Bool) (init : σ) : Nat → EM σ
  | 0 => .error "query nested too deeply"
  | fuel+1 => do
    -- a RIGHT or FULL JOIN's item: its rows are counted once, and the join marks those some earlier row matched
    let rightCount ← match rightIdx with
      | some r => do
        let (raw, cs, _) ← candidates (env.push frame0) (srcs.getD r default) (runs.getD r default) (subs.getD r none) none fuel
        pure (if raw.isEmpty then cs.size else raw.size)
      | none => pure 0
    let (acc, matched) ← if srcs.isEmpty then do pure (← emit init (env.push frame0) #[], #[])
      else joinFrom emit stop track (env.push frame0) srcs runs subs autos needs 0 #[] (init, Array.replicate rightCount false) fuel
    -- then its rows nothing matched, with NULLs for the items before it
    match rightIdx with
    | none => return acc
    | some r =>
      let src := srcs.getD r default
      let (raw, cs, _) ← candidates (env.push frame0) src (runs.getD r default) (subs.getD r none) none fuel
      let mut acc : σ × Array Bool := (acc, #[])
      for j in [0:rightCount] do
        if matched.getD j true then continue
        let e := env.push (bindCand src need frame0 raw cs j)
        let mut ok := true
        for k in [0:r+1] do
          unless ← (runs.getD k default).conds e do ok := false; break
        let refs : Array RowRef := if track then (Array.replicate r none).push raw[j]? else #[]
        if ok then acc ← joinFrom emit stop track e srcs runs subs autos needs (r+1) refs acc fuel
      return acc.1

mutual
/-- An expression's value (compiled, then run once). -/
def eval (env : Env) : CExpr → Nat → EM Value
  | _, 0 => .error "expression nested too deeply"
  | e, fuel+1 => (e.compile (fun env q => runSel env q fuel) fuel) env

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
    let vs := sortBy ((vs.filter (!·.isNull)).map (Value.applyCmpAff aff)) (cmpValues coll)
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
  | .select srcs pre filters g gc h cols rc order aggs isAgg d w ws, fuel+1 => do
    let hs (es : Array CExpr) : EM (Array CExpr) := es.mapM fun e => hoist env e fuel
    let srcs ← srcs.mapM fun (s : CSource) => (match s with
      | .table r n ipk rc dv base acc left right lay on => do
        let acc : Access CExpr ← match acc with
          | .rowidEq e => do pure (Access.rowidEq (← hoist env e fuel))
          | .rowidIn items => do pure (Access.rowidIn (← hs items))
          | a => pure a
        return CSource.table r n ipk rc dv base acc left right lay (← hs on)
      | s => pure s : EM CSource)
    let h' ← match h with
      | some x => do let r ← hoist env x fuel; pure (some r)
      | none => pure none
    return .select srcs (← hs pre) (← filters.mapM hs) (← hs g) gc h' (← hs cols) rc (← hs order) aggs isAgg d w ws

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
        let i ← limitInt (← eval env e fuel)
        pure (if i < 0 then none else some i.toNatClampNeg)
      | none => pure none
    -- LIMIT 0: no row is read, nothing evaluated (not even OFFSET)
    if lim == some 0 then return #[]
    let off ← match offset with
      | some e => do let i ← limitInt (← eval env e fuel); pure i.toNatClampNeg
      | none => pure 0
    let hint := if cores.size == 1 && dirs.isEmpty then lim.map (· + off) else none
    -- one core puts its own rows in ORDER BY's order
    let ord := if cores.size == 1 && !dirs.isEmpty then some (dirs, lim.map (· + off)) else none
    let mut acc : Array (Row × Row) := #[]
    let mut i := 0
    for core in cores do
      let core ← hoistCore env core fuel
      let rs ← runCore env none ord core (if i == 0 then hint else none) (if cores.size == 1 && dirs.isEmpty then off else 0) fuel
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
    let sorted := if dirs.isEmpty || ord.isSome then acc else orderRows dirs (lim.map (· + off)) acc
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
      | some e => do let i ← limitInt (← eval env e fuel); pure (if i < 0 then none else some i.toNatClampNeg)
      | none => pure none
    let anchor ← hoistCore env anchor fuel
    let init := (← runCore env none none anchor none 0 fuel).map (·.1)
    -- the recursive core runs once per queued row: compiled once
    let recurC := recur.compile (fun env q => runSel env q fuel) fuel
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
      let rs := (← runCore env' (some recurC) none recur none 0 fuel).map (·.1)
      for r in rs do
        if distinct && result.any (cmpRows · r == .eq) then continue
        result := result.push r
    return match lim with | some l => result.extract 0 l | none => result

/-- Runs one core: each result row with its ORDER BY keys. `pre?`: the core compiled already; `ord`: the rows are the whole
SELECT's, to be put in ORDER BY's order here (only the first `n` of them, when bounded); `hint`: enough rows (a LIMIT
with no ORDER BY). -/
def runCore (env : Env) (pre? : Option CoreRun) (ord : Option (Array (Bool × Bool × Collation) × Option Nat)) :
    CCore → Option Nat → Nat → Nat → EM (Array (Row × Row))
  | _, _, _, 0 => .error "query nested too deeply"
  | .values rows order, _, _, fuel+1 => do
    let mut out := #[]
    for r in rows do
      let vs ← r.mapM fun e => eval env e fuel
      out := out.push (vs, order.map (vs.getD · .null))
    return match ord with | some (dirs, bound) => orderRows dirs bound out | none => out
  | .select srcs pre filters groupBy gcolls having cols rcolls order aggs isAgg distinct width wins, hint, skip, fuel+1 => do
    let frame0 : Row := Array.replicate width .null
    -- the core's expressions, compiled once (or by the caller, for all its runs)
    let cr := pre?.getD ((CCore.select srcs pre filters groupBy gcolls having cols rcolls order aggs isAgg distinct width
      wins).compile (fun env q => runSel env q fuel) fuel)
    let preOk ← cr.pre (env.push frame0)
    unless preOk do
      if isAgg && groupBy.isEmpty then pure () else return #[]
    -- FROM subqueries run once
    let subs ← srcs.mapM fun s => match s with
      | .sub q _ _ _ _ _ _ => do let r ← runSel env q fuel; pure (some r)
      | _ => pure none
    -- transient indexes, built once (and only once some row reaches their item)
    let autos := srcs.mapIdx fun i s =>
      let keys := s.autoKeys
      if keys.isEmpty then none else some <| Thunk.mk fun _ => match s with
        | .table root _ _ _ _ _ _ _ _ _ _ => buildAuto s width keys (BTree.foldTable env.pager root #[] fun acc k r => acc.push (k, r)) #[]
        | .sub .. => buildAuto s width keys #[] ((subs.getD i none).getD #[])
        | .cte id .. => buildAuto s width keys #[] (env.ctes.getD id #[])
        | _ => default
    let rightIdx := srcs.findIdx? isRightOuter
    let hint := if isAgg || !order.isEmpty || !wins.isEmpty || rightIdx.isSome then none else hint
    let ⟨_, runs, groupByC, aggRuns, havingC, colsC, orderC, need, needs, late, keySrcs⟩ := cr
    -- ORDER BY of plain rows: each joined row goes into the sorter as the join makes it, its keys packed in a record (a
    -- key that is a table column read from the record in place) and its computed result columns evaluated; the columns
    -- only plain result columns and keys read are decoded once it is output
    if let some (dirs, bound) := ord then
      if !isAgg && !distinct && wins.isEmpty then
        let minus (m : Array Bool) : Array Bool := m.mapIdx fun k b => b && !late.getD k false
        let needs := needs.map fun (f, r) => (minus f, minus r)
        let plain : Array (Option Nat) := cols.map fun c => match c with | .col 0 s => some s | _ => none
        let computed : Array CFn := (cols.zip colsC).filterMap fun (c, f) => match c with | .col 0 _ => none | _ => some f
        let keyFns : Array CFn := (keySrcs.zip orderC).filterMap fun (k, f) => match k with | .expr _ => some f | _ => none
        let emit (st : Sorter) (e : Env) (refs : Array RowRef) : EM Sorter := do
          let vals ← computed.mapM (· e)
          let ks ← keyFns.mapM (· e)
          let seq := st.seq
          match bound with
          | none =>
            let en : SortEntry := { key := keyRecord keySrcs refs ks, seq, vals, frame := e.top, refs }
            return { rows := st.rows.push en, seq := seq + 1 }
          | some n =>
            if st.rows.size < n then
              let en : SortEntry := { key := keyRecord keySrcs refs ks, seq, vals, frame := e.top, refs }
              let rows := siftUp (cmpEntry dirs) (st.rows.push en) st.rows.size (n + 1)
              return { rows, seq := seq + 1 }
            -- full: a row below the largest kept one takes its place (its keys are packed only then)
            match st.rows[0]? with
            | some w =>
              if cmpKeyCand dirs keySrcs refs ks w.key == .gt then
                let en : SortEntry := { key := keyRecord keySrcs refs ks, seq, vals, frame := e.top, refs }
                let rows := siftDown (cmpEntry dirs) (st.rows.setIfInBounds 0 en) 0 (n + 1)
                return { rows, seq := seq + 1 }
              else return { st with seq := seq + 1 }
            | none => return { st with seq := seq + 1 }
        let track := late.any id || keySrcs.any (!· matches .expr _)
        let st ← if !preOk then pure ({} : Sorter)
          else joinAll emit (fun _ => false) track rightIdx env frame0 srcs runs subs autos needs need {} fuel
        return (sortBy st.rows (cmpEntry dirs)).map fun en =>
          let fr := bindLate srcs late en.frame en.refs
          let row := (plain.foldl (fun ((row : Row), j) p => match p with
            | some s => (row.push (fr.getD s .null), j)
            | none => (row.push (en.vals.getD j .null), j + 1)) (#[], 0)).1
          (row, #[])
    -- DISTINCT rows: each joined row's result passed on at its first occurrence (an ordered set keeps the results seen),
    -- so a LIMIT stops the scan
    if distinct && !isAgg && wins.isEmpty then
      let emit (st : Array (Row × Row) × Std.TreeSet Row (cmpRowsColl rcolls)) (e : Env) (_ : Array RowRef) :
          EM (Array (Row × Row) × Std.TreeSet Row (cmpRowsColl rcolls)) := do
        let (rows, seen) := st
        let vs ← colsC.mapM (· e)
        let (dup, seen) := seen.containsThenInsert vs
        if dup then return (rows, seen)
        return (rows.push (vs, ← orderC.mapM (· e)), seen)
      let (rows, _) ← if !preOk then pure (#[], {})
        else joinAll emit (fun st => hint.any (st.1.size ≥ ·)) false rightIdx env frame0 srcs runs subs autos needs need (#[], {}) fuel
      return match ord with | some (dirs, bound) => orderRows dirs bound rows | none => rows
    -- each result row's environment: its frame, or (aggregates) its group's
    let envs : Array Env ← if !isAgg then do
        let frames ← if !preOk then pure #[] else
          joinAll (fun (rows : Array Row) e _ => pure (rows.push e.top)) (fun rows => hint.any (rows.size ≥ ·)) false rightIdx env
            frame0 srcs runs subs autos needs need #[] fuel
        pure (frames.map env.push)
      else do
      -- each joined row stepped into its group as the join makes it
      let dd := aggRuns.map fun a => a.args.map fun _ => a.coll
      let inputs (e : Env) : EM (Array (Option (Array Value × Array Bool))) := aggRuns.mapM fun a => do
        -- a FILTER (WHERE f) skips the rows f is not true for
        if let some f := a.filter then
          if !(← f e) then return none
        -- (a JSON aggregate sees which arguments are JSON)
        if a.json then
          let vjs ← a.argsJ.mapM (· e)
          return some (vjs.map (·.1), vjs.map (·.2))
        return some (← a.args.mapM (· e), #[])
      let fresh : Group dd := { accs := aggRuns.map fun _ => {}, frame := frame0 }
      -- the planner's min()/max() early-out: an aggregate core whose item is read in order stops after one joined row
      let minMax := match srcs with
        | #[.table _ _ _ _ _ _ (.ordered ..) _ _ _ _] => true
        | _ => false
      -- a group's result: its aggregates' values, unless HAVING rejects it
      let finish (g : Group dd) : EM (Option Env) := do
        let vals ← (aggRuns.zip g.accs).mapM fun (a, acc) => aggFinal a.name acc
        let e := { (env.push g.frame) with aggs := vals, aggJson := aggRuns.map (·.json) }
        if let some h := havingC then
          if !(← h e) then return none
        return some e
      if groupBy.isEmpty then
        let g ← if !preOk then pure fresh else
          joinAll (fun (g : Group dd) e _ => do return g.step aggRuns (← inputs e) e.top) (fun g => minMax && 1 ≤ g.n) false
            rightIdx env frame0 srcs runs subs autos needs need fresh fuel
        pure (← finish g).toArray
      else
        -- the groups in an ordered map keyed by their GROUP BY values: they come out in its order
        let groups ← joinAll (fun (m : Std.TreeMap Row (Group dd) (cmpRowsColl gcolls)) e _ => do
            let key ← groupByC.mapM (· e)
            let ins ← inputs e
            return m.alter key fun g => some ((g.getD fresh).step aggRuns ins e.top))
          (fun _ => false) false rightIdx env frame0 srcs runs subs autos needs need {} fuel
        groups.foldlM (fun out _ g => do
          match ← finish g with
          | some e => return out.push e
          | none => return out) #[]
    -- window functions, over all the result rows
    let winCols ← wins.mapM fun w => winColumn envs w fuel
    let mut out := #[]
    -- (rows no one asked for, below the OFFSET: none of their expressions run)
    let skip := if isAgg || distinct || !wins.isEmpty then 0 else skip
    for i in [0:envs.size] do
      if i < skip then
        out := out.push (#[], #[])
        continue
      let e := { (envs.getD i env) with wins := winCols.map (·.getD i .null) }
      let vs ← colsC.mapM (· e)
      let ks ← orderC.mapM (· e)
      out := out.push (vs, ks)
    let rows := if distinct then firstRows rcolls out else out
    return match ord with | some (dirs, bound) => orderRows dirs bound rows | none => rows

/-- A window function's value for each result row: rows ordered by partition and ORDER BY keys, peers grouped, and the
frame of each row found (ROWS, RANGE or GROUPS, with EXCLUDE). -/
def winColumn (envs : Array Env) (w : CWin) : Nat → EM (Array Value)
  | 0 => .error "query nested too deeply"
  | fuel+1 => do
    let .mk name distinct star args filter part pcolls ord dirs units start finish excl := w
    let n := envs.size
    let sub : SubRun := fun env q => runSel env q fuel
    let comp (xs : Array CExpr) : Array CFn := xs.map (·.compile sub fuel)
    let (partC, ordC, argsC) := (comp part, comp ord, comp args)
    let pk ← envs.mapM fun e => partC.mapM (· e)
    let ok ← envs.mapM fun e => ordC.mapM (· e)
    let av ← envs.mapM fun e => argsC.mapM (· e)
    let isJ := Json.isJsonAgg name
    let argsJ := args.map (·.compileJson sub fuel)
    let aj ← if isJ then envs.mapM fun e => argsJ.mapM fun x => do pure (← x e).2 else pure #[]
    -- one row into an aggregate (a JSON one with its arguments' subtypes)
    let step := aggStepOf name star .binary
    let stepW (acc : AggAcc) (row : Nat) (vs : Array Value) (at_ : Nat) : AggAcc :=
      if isJ then { acc with json := Json.aggStep name acc.json vs (aj.getD row #[]) } else step acc vs at_
    let filterC := filter.map (·.compileTrue sub fuel)
    let fv ← envs.mapM fun e => match filterC with
      | some f => f e
      | none => pure true
    let boundC (b : CBound) : Option CFn := match b with
      | .preceding x | .following x => some (x.compile sub fuel)
      | _ => none
    let (startC, finishC) := (boundC start, boundC finish)
    let offs ← envs.mapM fun e => do
      let o (b : Option CFn) : EM Int := match b with
        | some x => do
          let v ← x e
          match v with
          | .int i => if i < 0 then throw "frame starting offset must be a non-negative integer" else pure i.toInt
          | .real r => if r < 0 then throw "frame starting offset must be a non-negative number" else pure r.toInt64.toInt
          | _ => throw "frame starting offset must be a non-negative integer"
        | none => pure 0
      pure (← o startC, ← o finishC)
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

end

end LSql

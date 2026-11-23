import LSql.Num
import LSql.Compare
import LSql.Ast
/-! Value semantics: affinity (datatype3.html §3), text conversion, arithmetic (vdbe.c OP_Add..), truth, LIKE and GLOB
(func.c patternCompare), and the scalar SQL functions (func.c, the math functions of func.c's SQLITE_ENABLE_MATH_FUNCTIONS). -/
namespace LSql

/-- Column affinity, and an expression's (`none`: no affinity). -/
inductive Aff where
  | none | text | numeric | integer | real | blob
  deriving DecidableEq, Repr, Inhabited

/-- The affinity of a declared column type (sqlite3AffinityType): INT, then CHAR/CLOB/TEXT, then BLOB or no type, then
REAL/FLOA/DOUB, else NUMERIC. -/
def Aff.ofType (t : String) : Aff :=
  let u := t.toUpper
  if (u.splitOn "INT").length > 1 then .integer
  else if (u.splitOn "CHAR").length > 1 || (u.splitOn "CLOB").length > 1 || (u.splitOn "TEXT").length > 1 then .text
  else if (u.splitOn "BLOB").length > 1 || u.toList.all Char.isWhitespace then .blob
  else if (u.splitOn "REAL").length > 1 || (u.splitOn "FLOA").length > 1 || (u.splitOn "DOUB").length > 1 then .real
  else .numeric

def Aff.isNumeric : Aff → Bool
  | .numeric | .integer | .real => true
  | _ => false

namespace Value

/-- A value as text (sqlite3_value_text): numbers rendered as sqlite renders them, blobs' bytes read as text. -/
def toText : Value → String
  | null => ""
  | int i => Num.int64ToText i
  | real f => Num.fmtReal f
  | text s => s
  | blob b => textOfBytes b

/-- A value as bytes (sqlite3_value_blob). -/
def toBytes : Value → ByteArray
  | blob b => b
  | text s => s.toUTF8
  | null => ByteArray.empty
  | v => v.toText.toUTF8

/-- A real that is an integer (and fits) becomes an integer: what NUMERIC and INTEGER affinity do to reals. -/
def realToIntIfExact (f : Float) : Value :=
  if f > -9223372036854775808.0 && f < 9223372036854775808.0 then
    let i := f.toInt64
    if i.toFloat == f then .int i else .real f
  else .real f

/-- Applies a column affinity to a value (on storage, and to a comparison's operand). -/
def applyAff (a : Aff) (v : Value) : Value :=
  match a, v with
  | .text, int _ | .text, real _ => text v.toText
  | .numeric, text s | .integer, text s => (Num.textToNumeric? s).getD v
  | .numeric, real f | .integer, real f => realToIntIfExact f
  | .real, text s => match Num.textToNumeric? s with
    | some (int i) => real i.toFloat
    | some x => x
    | none => v
  | .real, int i => real i.toFloat
  | _, _ => v

/-- sqlite3VdbeBooleanValue: a number is true when non-zero, text by its numeric prefix; NULL is none. -/
def truth? : Value → Option Bool
  | null => none
  | int i => some (i != 0)
  | real f => some (f != 0)
  | v => match Num.numericValue v with
    | int i => some (i != 0)
    | real f => some (f != 0)
    | _ => some false

end Value

/-! ## Arithmetic -/

/-- The numeric value an operand has in arithmetic: none for NULL. -/
@[inline] def numOf (v : Value) : Value := match v with
  | .int _ | .real _ | .null => v
  | _ => Num.numericValue v

@[inline] def toF : Value → Float
  | .int i => i.toFloat
  | .real f => f
  | _ => 0

/-- A real result that is NaN is NULL (sqlite stores no NaN). -/
@[inline] def realV (f : Float) : Value := if f.isNaN then .null else .real f

def arith (op : BinOp) (a b : Value) : Value :=
  match numOf a, numOf b with
  | .null, _ | _, .null => .null
  | .int x, .int y =>
    match op with
    | .add => match Num.addInt? x y with | some r => .int r | none => realV (x.toFloat + y.toFloat)
    | .sub => match Num.subInt? x y with | some r => .int r | none => realV (x.toFloat - y.toFloat)
    | .mul => match Num.mulInt? x y with | some r => .int r | none => realV (x.toFloat * y.toFloat)
    | .div => if y == 0 then .null else match Num.divInt? x y with | some r => .int r | none => realV (x.toFloat / y.toFloat)
    | .mod => if y == 0 then .null else match Num.remInt? x y with | some r => .int r | none => .int 0
    | _ => .null
  | x, y =>
    match op with
    | .add => realV (toF x + toF y)
    | .sub => realV (toF x - toF y)
    | .mul => realV (toF x * toF y)
    | .div => if toF y == 0 then .null else realV (toF x / toF y)
    | .mod =>
      let ix := Num.castToInt x
      let iy := Num.castToInt y
      if iy == 0 then .null else
      match Num.remInt? ix iy with
      | some r => realV r.toFloat
      | none => .real 0
    | _ => .null

/-- The integer an operand of a bit operator is. -/
@[inline] def intOf (v : Value) : Option Int64 := match v with
  | .null => none
  | .int i => some i
  | v => some (Num.castToInt v)

def bitop (op : BinOp) (a b : Value) : Value :=
  match intOf a, intOf b with
  | some x, some y =>
    match op with
    | .bitAnd => .int (x &&& y)
    | .bitOr => .int (x ||| y)
    | .shl => shift x y
    | .shr => shift x (-y)
    | _ => .null
  | _, _ => .null
where
  /-- shifts left by `n` (right for negative `n`, sign-filling), 0 or -1 past 63 -/
  shift (x n : Int64) : Value :=
    if n ≥ 64 then .int 0
    else if n ≥ 0 then .int (x <<< n)
    else if n ≤ -64 then .int (if x < 0 then -1 else 0)
    else .int (x >>> (-n))

def concatV (a b : Value) : Value :=
  match a, b with
  | .null, _ | _, .null => .null
  | _, _ => .text (a.toText ++ b.toText)

def negV : Value → Value
  | .null => .null
  | .int i => if i == -9223372036854775808 then .real 9223372036854775808.0 else .int (-i)
  | .real f => .real (-f)
  | v => match Num.numericValue v with
    | .int i => if i == -9223372036854775808 then .real 9223372036854775808.0 else .int (-i)
    | .real f => .real (-f)
    | _ => .int 0

/-! ## LIKE and GLOB (func.c patternCompare), on bytes; LIKE folds ASCII case only, as sqlite's default. -/

/-- Bytes of the UTF-8 character starting at `i`. -/
@[inline] def charLen (b : ByteArray) (i : Nat) : Nat :=
  let c := rd b i
  if c < 0x80 then 1 else if c < 0xE0 then 2 else if c < 0xF0 then 3 else 4

/-- Whether `n` bytes of `a` at `i` equal those of `b` at `j` (ASCII case folded when `fold`). -/
def bytesEq (a : ByteArray) (i : Nat) (b : ByteArray) (j : Nat) (fold : Bool) : Nat → Bool
  | 0 => true
  | n+1 =>
    let x := rd a i
    let y := rd b j
    (if fold then foldCase x == foldCase y else x == y) && bytesEq a (i+1) b (j+1) fold n

/-- LIKE: `%` any run, `_` one character, `esc` makes the next character literal. -/
def likeMatch (pat str : ByteArray) (esc : Option UInt8) : Bool :=
  go 0 0 (pat.size * (str.size + 1) + pat.size + str.size + 2)
where
  go (p s : Nat) : Nat → Bool
    | 0 => false
    | fuel+1 =>
      if p ≥ pat.size then s ≥ str.size else
      let c := rd pat p
      if esc == some c then
        -- escaped literal
        let p' := p + 1
        if p' ≥ pat.size then false else
        let n := charLen pat p'
        if s + n ≤ str.size && bytesEq pat p' str s true n then go (p' + n) (s + n) fuel else false
      else if c == 37 then -- %
        let p1 := p + 1
        if p1 ≥ pat.size then true else
        anyFrom p1 s (str.size - s + 1) fuel
      else if c == 95 then -- _
        if s ≥ str.size then false else go (p + 1) (s + charLen str s) fuel
      else
        let n := charLen pat p
        if s + n ≤ str.size && bytesEq pat p str s true n then go (p + n) (s + n) fuel else false
  termination_by fuel => (fuel, 0)
  /-- whether the pattern from `p` matches the string from some position in `[s, s + k)` -/
  anyFrom (p s : Nat) : Nat → Nat → Bool
    | 0, _ => false
    | _, 0 => false
    | k+1, fuel+1 => go p s fuel || anyFrom p (s + 1) k (fuel + 1)
  termination_by k fuel => (fuel, k)

/-- The code point of the UTF-8 character at `i`. -/
def codeAt (b : ByteArray) (i : Nat) : Nat :=
  let c := (rd b i).toNat
  match charLen b i with
  | 1 => c
  | 2 => (c &&& 0x1F) <<< 6 ||| ((rd b (i+1)).toNat &&& 0x3F)
  | 3 => (c &&& 0x0F) <<< 12 ||| ((rd b (i+1)).toNat &&& 0x3F) <<< 6 ||| ((rd b (i+2)).toNat &&& 0x3F)
  | _ => (c &&& 0x07) <<< 18 ||| ((rd b (i+1)).toNat &&& 0x3F) <<< 12 ||| ((rd b (i+2)).toNat &&& 0x3F) <<< 6
          ||| ((rd b (i+3)).toNat &&& 0x3F)

/-- GLOB: `*`, `?`, `[...]` with ranges and `^` negation; case-sensitive. -/
def globMatch (pat str : ByteArray) : Bool :=
  go 0 0 (pat.size * (str.size + 1) + pat.size + str.size + 2)
where
  /-- whether the class at `p` (after `[`) matches code point `c`, and the position after `]` -/
  cls (p : Nat) (c : Nat) : Option (Bool × Nat) :=
    let (neg, p) := if rd pat p == 94 then (true, p + 1) else (false, p)
    -- a ] first is a literal
    let (hit, p, first) := (false, p, true)
    clsLoop neg hit p first c (pat.size + 1)
  clsLoop (neg hit : Bool) (p : Nat) (first : Bool) (c : Nat) : Nat → Option (Bool × Nat)
    | 0 => none
    | fuel+1 =>
      if p ≥ pat.size then none else
      let x := rd pat p
      if x == 93 && !first then some (hit != neg, p + 1) else
      let lo := codeAt pat p
      let p1 := p + charLen pat p
      if rd pat p1 == 45 && p1 + 1 < pat.size && rd pat (p1 + 1) != 93 then
        let hi := codeAt pat (p1 + 1)
        let p2 := p1 + 1 + charLen pat (p1 + 1)
        clsLoop neg (hit || (lo ≤ c && c ≤ hi)) p2 false c fuel
      else clsLoop neg (hit || lo == c) p1 false c fuel
  go (p s : Nat) : Nat → Bool
    | 0 => false
    | fuel+1 =>
      if p ≥ pat.size then s ≥ str.size else
      let c := rd pat p
      if c == 42 then -- *
        let p1 := p + 1
        if p1 ≥ pat.size then true else
        anyFrom p1 s (str.size - s + 1) fuel
      else if c == 63 then -- ?
        if s ≥ str.size then false else go (p + 1) (s + charLen str s) fuel
      else if c == 91 then -- [
        if s ≥ str.size then false else
        match cls (p + 1) (codeAt str s) with
        | some (true, p') => go p' (s + charLen str s) fuel
        | _ => false
      else
        let n := charLen pat p
        if s + n ≤ str.size && bytesEq pat p str s false n then go (p + n) (s + n) fuel else false
  termination_by fuel => (fuel, 0)
  anyFrom (p s : Nat) : Nat → Nat → Bool
    | 0, _ => false
    | _, 0 => false
    | k+1, fuel+1 => go p s fuel || anyFrom p (s + 1) k (fuel + 1)
  termination_by k fuel => (fuel, k)

/-! ## Scalar functions -/

def hexDigit (n : Nat) : Char := "0123456789ABCDEF".toList.getD n '0'

def hexOf (b : ByteArray) : String :=
  b.foldl (fun s c => (s.push (hexDigit (c.toNat / 16))).push (hexDigit (c.toNat % 16))) ""

/-- quote(): an SQL literal for the value. -/
def quoteV : Value → String
  | .null => "NULL"
  | .int i => Num.int64ToText i
  | .real f => Num.fmtReal f |> fun s => s
  | .text s => "'" ++ s.replace "'" "''" ++ "'"
  | .blob b => "X'" ++ hexOf b ++ "'"

/-- Characters of a string (code points), for length/substr/instr on text. -/
def charCount (s : String) : Nat := s.length

/-- substr(X, Y [, Z]) on characters (text) or bytes (blobs), sqlite's 1-based and negative positions. -/
def substrV (x : Value) (y : Int64) (z : Option Int64) : Value :=
  match x with
  | .null => .null
  | .blob b => .blob (cut b.size y z |> fun (a, n) => b.extract a (a + n))
  | v =>
    let s := v.toText
    let (a, n) := cut s.length y z
    .text (String.ofList ((s.toList.drop a).take n))
where
  /-- start offset and length within `len` -/
  cut (len : Nat) (y : Int64) (z : Option Int64) : Nat × Nat :=
    let len : Int := len
    let y : Int := y.toInt
    let (p1, z) : Int × Int := match z with
      | none => (if y < 0 then y + len else if y > 0 then y - 1 else 0, if y == 0 then len - 1 + 1 else len)
      | some z0 =>
        let z0 : Int := z0.toInt
        if y < 0 then
          let p := y + len
          if z0 < 0 then (p + z0, -z0) else (p, z0)
        else if y > 0 then
          if z0 < 0 then (y - 1 + z0, -z0) else (y - 1, z0)
        else -- y = 0: positions before the first character count
          if z0 < 0 then (z0, -z0) else (0, z0 - 1)
    let (p1, z) := if p1 < 0 then (0, z + p1) else (p1, z)
    let z := max 0 z
    let p1 := min p1 len
    let z := min z (len - p1)
    (p1.toNat, z.toNat)

def trimChars (s : String) (chars : List Char) (left right : Bool) : String :=
  let cs := s.toList
  let cs := if left then cs.dropWhile (chars.contains ·) else cs
  let cs := if right then (cs.reverse.dropWhile (chars.contains ·)).reverse else cs
  String.ofList cs

def lowerAscii (s : String) : String := s.map fun c => if c ≥ 'A' && c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c
def upperAscii (s : String) : String := s.map fun c => if c ≥ 'a' && c ≤ 'z' then Char.ofNat (c.toNat - 32) else c

/-- instr(X, Y): 1-based position of Y in X (characters for text, bytes for blobs), 0 when absent. -/
def instrV (x y : Value) : Value :=
  match x, y with
  | .null, _ | _, .null => .null
  | .blob a, .blob b => .int (findBytes a b).toInt64
  | _, _ =>
    let a := x.toText
    let b := y.toText
    let bs := b.toList
    let rec go (cs : List Char) (i : Nat) : Nat :=
      match cs with
      | [] => if bs.isEmpty then i else 0
      | c :: rest => if bs.isPrefixOf (c :: rest) then i else go rest (i + 1)
    .int (go a.toList 1).toInt64
where
  findBytes (a b : ByteArray) : Nat :=
    match (List.range (a.size + 1 - b.size)).find? (fun i => (List.range b.size).all fun k => rd a (i + k) == rd b k) with
    | some i => if b.size ≤ a.size then i + 1 else 0
    | none => 0

/-- unicode(X): the code point of X's first character. -/
def unicodeV (v : Value) : Value :=
  match v with
  | .null => .null
  | v => match v.toText.toList.head? with
    | some c => if c.toNat == 0 then .null else .int c.toNat.toInt64
    | none => .null

def charV (args : Array Value) : Value :=
  .text (String.ofList (args.toList.map fun v => Char.ofNat (Num.castToInt v).toNatClampNeg))

/-- round(X [, N]). -/
def roundV (x : Value) (n : Option Value) : Value :=
  match x, n with
  | .null, _ => .null
  | _, some .null => .null
  | x, n =>
    let digits : Int := match n with | some v => (Num.castToInt v).toInt | none => 0
    match numOf x with
    | .int i => if digits ≥ 0 || true then (if n.isNone || digits ≥ 0 then .real i.toFloat else .real (Num.roundReal i.toFloat digits)) else .null
    | .real f => .real (Num.roundReal f digits)
    | _ => .real 0

def absV : Value → Except String Value
  | .null => .ok .null
  | .int i => if i == -9223372036854775808 then .error "integer overflow" else .ok (.int (if i < 0 then -i else i))
  | .real f => .ok (.real f.abs)
  | v => .ok (.real (Num.castToReal v).abs)

/-- A math function of one real argument (NULL in, NULL out; text converted). -/
def math1 (f : Float → Float) (v : Value) : Value :=
  match numOf v with
  | .null => .null
  | x => realV (f (toF x))

def signV (v : Value) : Value :=
  match (match v with | .text _ | .blob _ => Value.applyAff .numeric v | v => v) with
  | .int i => .int (if i > 0 then 1 else if i < 0 then -1 else 0)
  | .real f => .int (if f > 0 then 1 else if f < 0 then -1 else 0)
  | _ => .null

/-- ceil/floor/trunc keep integers as they are. -/
def intRound (f : Float → Float) (v : Value) : Value :=
  match numOf v with
  | .int i => .int i
  | .real x => .real (f x)
  | _ => .null

def unhexV (v : Value) : Value :=
  match v with
  | .null => .null
  | v =>
    let s := v.toText.toList
    let hv (c : Char) : Option Nat :=
      if c ≥ '0' && c ≤ '9' then some (c.toNat - 48) else if c ≥ 'a' && c ≤ 'f' then some (c.toNat - 87)
      else if c ≥ 'A' && c ≤ 'F' then some (c.toNat - 55) else none
    let rec go : List Char → ByteArray → Option ByteArray
      | [], acc => some acc
      | a :: b :: rest, acc => match hv a, hv b with
        | some x, some y => go rest (acc.push (x * 16 + y).toUInt8)
        | _, _ => none
      | [_], _ => none
    match go s ByteArray.empty with
    | some b => .blob b
    | none => .null

end LSql

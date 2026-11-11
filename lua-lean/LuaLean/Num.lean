/-! Lua numbers: IEEE doubles, as LuaJIT 2.1 has them. A number is a 32-bit integer (`int`) or a double (`flt`), as
in LuaJIT's dual-number mode (arm64's default); only the sign of a zero tells them apart (`0 * -1` is 0,
`0.5 * 0 * -1` is -0). A single-number build (x86-64's default) keeps doubles only, which `.int i` models exactly but
in one place: there an integer product of 0 with a negative factor is -0 (`Target`, `mul`). Integers come from
literals and `tonumber` (an integral value in range that is not -0), from constant folding in the parser
(`foldArith`), and from integer +, -, * and % that stay in range; / and ^ give doubles, and a double is never
narrowed back. Formatting (`%.14g`, `%f`, `%e`, `%g`) and reading (`tonumber`, literals) work on the exact binary
value with round-half-even, as C's printf and LuaJIT's strscan do. -/

namespace Lua

inductive Num where | int (i : Int) | flt (f : Float)
  deriving Inhabited

/-- the LuaJIT build: dual-number (arm64's default) or single-number (x86-64's default), told apart by
`local z, n = 0, -1; return 1/(z*n)` (inf, -inf) -/
inductive Target where | dual | single
  deriving DecidableEq, Inhabited

namespace Num

def isNegZero (f : Float) : Bool := f == 0 && 1 / f < 0

/-- the exact integer of an integral double -/
def floatToInt (f : Float) : Int :=
  if f < 0 then -(((-f).floor).toUInt64.toNat : Int) else (f.floor.toUInt64.toNat : Int)

def inInt32 (i : Int) : Bool := -2147483648 ≤ i && i < 2147483648

/-- an integer result: a 32-bit integer, or past that the double -/
def ofInt (i : Int) : Num := if inInt32 i then .int i else .flt (Float.ofInt i)

/-- LuaJIT's narrowing (STRSCAN_OPT_TOINT, constant folding): an integral double in range, not -0, is an integer -/
def narrow (f : Float) : Num :=
  if f.isFinite && f.floor == f && f.abs < 2147483648.5 && !isNegZero f then ofInt (floatToInt f) else .flt f

def toFloat : Num → Float
  | .int i => Float.ofInt i
  | .flt f => f

def add : Num → Num → Num
  | .int a, .int b => ofInt (a + b)
  | a, b => .flt (a.toFloat + b.toFloat)
def sub : Num → Num → Num
  | .int a, .int b => ofInt (a - b)
  | a, b => .flt (a.toFloat - b.toFloat)
def mul (t : Target) : Num → Num → Num
  | .int a, .int b => if t = .single ∧ a * b = 0 ∧ (a < 0 ∨ b < 0) then .flt (-0.0) else ofInt (a * b)
  | a, b => .flt (a.toFloat * b.toFloat)
def div (a b : Num) : Num := .flt (a.toFloat / b.toFloat)
/-- Lua 5.1: a - floor(a/b)*b -/
def fmod (x y : Float) : Float := x - (x / y).floor * y
def mod : Num → Num → Num
  | .int a, .int b => if b != 0 then ofInt (Int.fmod a b) else .flt (fmod (Float.ofInt a) 0)
  | a, b => .flt (fmod a.toFloat b.toFloat)
def pow (a b : Num) : Num := .flt (Float.pow a.toFloat b.toFloat)
def neg : Num → Num
  | .int 0 => .flt (-0.0)
  | .int a => ofInt (-a)
  | .flt f => .flt (-f)

def lt : Num → Num → Bool
  | .int a, .int b => a < b
  | a, b => a.toFloat < b.toFloat
def le : Num → Num → Bool
  | .int a, .int b => a ≤ b
  | a, b => a.toFloat ≤ b.toFloat
def eq : Num → Num → Bool
  | .int a, .int b => a == b
  | a, b => a.toFloat == b.toFloat

def floor : Num → Num
  | .int a => .int a
  | .flt f => .flt f.floor
def ceil : Num → Num
  | .int a => .int a
  | .flt f => .flt f.ceil

/-- lj_vm_foldarith on two constants, then the parser's rule: no NaN or -0 constant (`none`: not folded) -/
def foldArith (op : Nat) (a b : Num) : Option Num :=
  let x := a.toFloat
  let y := b.toFloat
  let n := match op with
    | 0 => x + y | 1 => x - y | 2 => x * y | 3 => x / y | 4 => fmod x y | _ => Float.pow x y
  if n.isNaN || isNegZero n then none else some (narrow n)

/-- unary minus on a constant (bcemit_unop): never a zero, which would fold to -0; an integer stays one (but -2^31),
a double flips its sign and is narrowed, as fs_fixup_k narrows every constant (-2^31 is the one that becomes an integer) -/
def foldNeg : Num → Option Num
  | .int 0 => none
  | .int k => some (if k == -2147483648 then .flt (-(Float.ofInt k)) else .int (-k))
  | .flt f => if f == 0 then none else some (narrow (-f))

#guard match foldNeg (.flt 2147483648) with | some (.int k) => k == -2147483648 | _ => false

/-- the integer a C cast gives a double in its range (truncation); 0 for inf and NaN -/
def trunc : Num → Int
  | .int a => a
  | .flt f => if f.isFinite then (if f < 0 then -floatToInt (-f).floor else floatToInt f.floor) else 0

-- ---------- exact decimal formatting ----------

/-- a finite double's magnitude as m * 2^e -/
def parts (f : Float) : Nat × Int :=
  let f := f.abs
  if f == 0 then (0, 0) else
  let (fr, ex) := f.frExp
  ((fr.scaleB 53).toUInt64.toNat, ex - 53)

/-- the magnitude as a fraction num / den -/
def ratio (f : Float) : Nat × Nat :=
  let (m, e) := parts f
  if e ≥ 0 then (m * 2 ^ e.toNat, 1) else (m, 2 ^ e.natAbs)

/-- num / den rounded to the nearest integer, ties to even -/
def roundDiv (num den : Nat) : Nat :=
  let q := num / den
  let r := num % den
  if 2 * r > den then q + 1 else if 2 * r < den then q else if q % 2 == 1 then q + 1 else q

def digits (n : Nat) : List Char := (Nat.toDigits 10 n)

def padLeft (c : Char) (w : Nat) (s : List Char) : List Char := List.replicate (w - s.length) c ++ s

/-- `%.<p>f` of a magnitude num/den -/
def fixedOf (num den p : Nat) (alt : Bool := false) : List Char :=
  let v := roundDiv (num * 10 ^ p) den
  let ds := padLeft '0' (p + 1) (digits v)
  let ip := ds.take (ds.length - p)
  let fp := ds.drop (ds.length - p)
  if p == 0 then ip ++ (if alt then ['.'] else []) else ip ++ ['.'] ++ fp

/-- the decimal exponent x with 10^x ≤ num/den < 10^(x+1), for num > 0 -/
def exp10 (num den : Nat) : Int :=
  if num ≥ den then
    -- (digits of num/den) - 1
    ((digits (num / den)).length : Int) - 1
  else
    -- the least k with num * 10^k ≥ den
    let rec go (k : Nat) (fuel : Nat) : Nat :=
      match fuel with
      | 0 => k
      | fuel + 1 => if num * 10 ^ k ≥ den then k else go (k + 1) fuel
    Int.neg (go 1 400)

/-- scaled: num/den * 10^s as a fraction -/
def scale (num den : Nat) (s : Int) : Nat × Nat :=
  if s ≥ 0 then (num * 10 ^ s.toNat, den) else (num, den * 10 ^ s.natAbs)

/-- `%.<p>e` digits and exponent of a magnitude: (d.ddd, x) after rounding -/
def sciOf (num den p : Nat) : Nat × Int :=
  if num == 0 then (0, 0) else
  let x := exp10 num den
  let (a, b) := scale num den (p - x)
  -- LuaJIT's nd_round: a tie whose cut digit is 10^9 or above in an integer rounds up (its scan for a nonzero
  -- rest starts at the cut's own 9-digit limb, which holds the 5); every other tie rounds to even
  let v := if num % den == 0 && x - p - 1 ≥ 9 && 2 * (a % b) == b then a / b + 1 else roundDiv a b
  if v ≥ 10 ^ (p + 1) then (v / 10, x + 1) else (v, x)

def expText (x : Int) : List Char :=
  (if x < 0 then ['-'] else ['+']) ++ padLeft '0' 2 (digits x.natAbs)

def sciText (num den p : Nat) (upper alt : Bool) : List Char :=
  let (v, x) := sciOf num den p
  let ds := padLeft '0' (p + 1) (digits v)
  let mant := [ds.head!] ++ (if p == 0 then (if alt then ['.'] else []) else ['.'] ++ ds.tail)
  mant ++ [if upper then 'E' else 'e'] ++ expText x

def stripZeros (s : List Char) : List Char :=
  if s.contains '.' then
    let r := (s.reverse.dropWhile (· == '0'))
    (if r.head? == some '.' then r.tail else r).reverse
  else s

/-- `%.<p>g` of a magnitude -/
def generalText (num den p : Nat) (upper alt : Bool) : List Char :=
  let p := if p == 0 then 1 else p
  let x := if num == 0 then 0 else (sciOf num den (p - 1)).2
  if x < p ∧ x ≥ -4 then
    let s := fixedOf num den (p - 1 - x).toNat alt
    if alt then s else stripZeros s
  else
    let s := sciText num den (p - 1) upper alt
    if alt then s else
      let (m, e) := s.span (fun c => c != 'e' && c != 'E')
      stripZeros m ++ e

/-- a double through a C conversion (f, e, E, g, G) of precision p, without sign; inf and nan as LuaJIT -/
def convMag (f : Float) (conv : Char) (p : Nat) (alt : Bool) : List Char :=
  if f.isNaN then "nan".toList else if f.isInf then "inf".toList else
  let (num, den) := ratio f
  match conv with
  | 'f' | 'F' => fixedOf num den p alt
  | 'e' => sciText num den p false alt
  | 'E' => sciText num den p true alt
  | 'G' => generalText num den p true alt
  | _ => generalText num den p false alt

def negative (f : Float) : Bool := f < 0 || isNegZero f || (f.isNaN && false)

/-- `%.14g`: tostring -/
def toText (n : Num) : List Char :=
  match n with
  | .int i => (if i < 0 then ['-'] else []) ++
    (if i.natAbs < 10 ^ 14 then digits i.natAbs else convMag (Float.ofNat i.natAbs) 'g' 14 false)
  | .flt f => (if negative f then ['-'] else []) ++ convMag f 'g' 14 false

/-- `%.17g`: every double distinct, for comparing results -/
def exactText (n : Num) : List Char :=
  match n with
  | .int i => (if i < 0 then ['-'] else []) ++ digits i.natAbs
  | .flt f => (if negative f then ['-'] else []) ++ convMag f 'g' 17 false

-- ---------- reading numbers ----------

/-- num / den as the nearest double, ties to even -/
def ofRatio (num den : Nat) : Float :=
  if num == 0 then 0 else
  -- k with 2^52 ≤ num * 2^k / den < 2^53
  let lg : Int := (num.log2 : Int) - (den.log2 : Int)
  let k0 : Int := 52 - lg
  let q k : Nat := if k ≥ 0 then roundDiv (num * 2 ^ k.toNat) den else roundDiv num (den * 2 ^ k.natAbs)
  let fl k : Nat := if k ≥ 0 then (num * 2 ^ k.toNat) / den else num / (den * 2 ^ k.natAbs)
  let k := if fl k0 ≥ 2 ^ 53 then k0 - 1 else if fl k0 < 2 ^ 52 then k0 + 1 else k0
  if k > 1074 then
    -- subnormal: granularity 2^-1074
    (Float.ofNat (q 1074)).scaleB (-1074)
  else if k < -971 then (1.0 / 0.0)
  else
    let v := q k
    (Float.ofNat v).scaleB (-k)

/-- C's fmod: x minus y times the truncated quotient, exact, with x's sign -/
def fmodC (x y : Float) : Float :=
  if x.isNaN || y.isNaN || !x.isFinite || y == 0 then 0.0 / 0.0
  else if !y.isFinite || x == 0 then x
  else
    let (nx, dx) := ratio x
    let (ny, dy) := ratio y
    let d := max dx dy
    let m := ofRatio ((nx * (d / dx)) % (ny * (d / dy))) d
    if x < 0 then -m else m

/-- C's modf: the integral part, truncated, and the rest, both with x's sign -/
def modfC (x : Float) : Float × Float :=
  if x.isNaN then (x, x) else
  let z : Float := if x < 0 || isNegZero x then -0.0 else 0.0
  if !x.isFinite then (x, z) else
  let i := if x < 0 then -(-x).floor else x.floor
  let r := x - i
  (i, if r == 0 then z else r)

/-- C's frexp: m in [0.5, 1) and e with x = m * 2^e; 0, inf and NaN with 0 -/
def frexpC (x : Float) : Float × Int :=
  if x == 0 || !x.isFinite then (x, 0) else x.frExp

def isSpace (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0b' || c == '\x0c'
def isDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'
def hexVal (c : Char) : Option Nat :=
  if isDigit c then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- a digit in any base up to 36 -/
def digitVal (c : Char) : Option Nat :=
  if isDigit c then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'z' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'Z' then some (c.toNat - 'A'.toNat + 10)
  else none

def lower (c : Char) : Char := if 'A' ≤ c && c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c

/-- digits in base b, and the rest -/
def spanDigits (b : Nat) : List Char → Nat → Nat → (Nat × Nat × List Char)
  | c :: s, acc, n =>
    match digitVal c with
    | some d => if d < b then spanDigits b s (acc * b + d) (n + 1) else (acc, n, c :: s)
    | none => (acc, n, c :: s)
  | [], acc, n => (acc, n, [])

/-- the exponent after its letter `p`, and the rest (no digits: no exponent, `p` left in the rest); none, so no
number, when its digits reach LuaJIT's STRSCAN_MAXEXP, 2^20 (`tonumber("1e1048576")` is nil) -/
def scanExp (p : Char) (r : List Char) : Option (Int × List Char) :=
  let (neg, r') := match r with | '-' :: q => (true, q) | '+' :: q => (false, q) | q => (false, q)
  let (ev, ne, r3) := spanDigits 10 r' 0 0
  if ne == 0 then some (0, p :: r) else if ev ≥ 1048576 then none else some (if neg then -(ev : Int) else ev, r3)

/-- an unsigned decimal or hex number at the start of s, and the rest (LuaJIT's lj_strscan, without its
FFI suffixes) -/
def scanNum (s : List Char) : Option (Float × List Char) :=
  match s with
  | '0' :: x :: r =>
    if x == 'x' || x == 'X' then
      let (ip, ni, r) := spanDigits 16 r 0 0
      let (fp, nf, r) := match r with
        | '.' :: r => spanDigits 16 r 0 0
        | r => (0, 0, r)
      if ni + nf == 0 then none else
      let m := ip * 16 ^ nf + fp
      match (match r with
        | p :: r => if p == 'p' || p == 'P' then scanExp p r else some (0, p :: r)
        | [] => some (0, [])) with
      | none => none
      | some (e, r) =>
      let e := e - 4 * nf
      some (if e ≥ 0 then ofRatio (m * 2 ^ e.toNat) 1 else ofRatio m (2 ^ e.natAbs), r)
    else dec s
  | _ => dec s
where
  dec (s : List Char) : Option (Float × List Char) :=
    let (ip, ni, r) := spanDigits 10 s 0 0
    let (fp, nf, r) := match r with
      | '.' :: r => spanDigits 10 r 0 0
      | r => (0, 0, r)
    if ni + nf == 0 then
      -- inf, infinity, nan
      let w := (s.take 8).map lower
      if w.take 8 == "infinity".toList then some (1.0 / 0.0, s.drop 8)
      else if w.take 3 == "inf".toList then some (1.0 / 0.0, s.drop 3)
      else if w.take 3 == "nan".toList then some (0.0 / 0.0, s.drop 3)
      else none
    else
    let m := ip * 10 ^ nf + fp
    match (match r with
      | p :: r' => if p == 'e' || p == 'E' then scanExp p r' else some (0, p :: r')
      | [] => some (0, [])) with
    | none => none
    | some (e, r) =>
    let e := e - nf
    let v := if m == 0 then 0.0 else if e > 400 then 1.0 / 0.0 else if e < -400 then 0.0 else
      if e ≥ 0 then ofRatio (m * 10 ^ e.toNat) 1 else ofRatio m (10 ^ e.natAbs)
    some (v, r)

/-- tonumber(s): blanks around, a sign, then the number and nothing else -/
def parse (s : List Char) : Option Num :=
  let s := s.dropWhile isSpace
  let (neg, s) := match s with | '-' :: r => (true, r) | '+' :: r => (false, r) | r => (false, r)
  match scanNum s with
  | some (f, r) => if r.all isSpace then some (narrow (if neg then -f else f)) else none
  | none => none

/-- the digits tonumber(s, base) hands strtoul: blanks around, then one sign (true: `-`) -/
def baseDigits (s : List Char) : Bool × List Char :=
  let s := (s.dropWhile isSpace).reverse.dropWhile isSpace |>.reverse
  match s with | '-' :: r => (true, r) | '+' :: r => (false, r) | r => (false, r)

/-- base 2 and a `0b` prefix before a binary digit, which glibc 2.38's strtoul reads (C23) and older C libraries
do not: the semantics stops the run there -/
def binPrefix (s : List Char) (b : Nat) : Bool :=
  b == 2 && match (baseDigits s).2 with | '0' :: c :: d :: _ => (c == 'b' || c == 'B') && (d == '0' || d == '1') | _ => false

/-- tonumber(s, base) for a base other than 10, as lib_base.c does it: strtoul on the digits (base 16 may start
`0x`), saturated at 2^64 - 1, then the sign; dual-number keeps an integer below 2^31 (-2^31 negated), single-number a
double (so `-0` is -0) -/
def parseBase (tgt : Target) (s : List Char) (b : Nat) : Option Num :=
  let (neg, s) := baseDigits s
  let s := s.map lower
  let s := match s with
    | '0' :: 'x' :: d :: r => if b == 16 && (digitVal d).any (· < 16) then d :: r else s
    | s => s
  let (v, n, r) := spanDigits b s 0 0
  if n == 0 || !r.isEmpty then none else
  let v := min v (2 ^ 64 - 1)
  if tgt == .dual && v < 2 ^ 31 + (if neg then 1 else 0) then some (.int (if neg then -(v : Int) else v))
  else let f := ofRatio v 1; some (.flt (if neg then -f else f))

end Num
end Lua

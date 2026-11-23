import LSql.Value

/-! sqlite's number and text conversions (util.c, vdbemem.c, vdbe.c, printf.c, func.c), following
sqlite 3.54: floating point text through sqlite3FpDecode / sqlite3Fp10Convert2, integer text through
sqlite3Atoi64, and the SQL printf() engine. All functions are total: loops are structural recursion
on a fuel bounded by the input size. -/

namespace LSql.Num

open LSql

/-! ### Byte helpers -/

/-- The byte at index i, or 0 past the end (a C string's terminator). -/
@[inline] def byteAt (b : ByteArray) (i : Nat) : UInt8 :=
  if h : i < b.size then b[i] else 0

/-- sqlite3Isspace: tab, newline, vertical tab, form feed, carriage return and space. -/
@[inline] def isSpace (c : UInt8) : Bool := c == 32 || (9 ≤ c && c ≤ 13)

@[inline] def isDigit (c : UInt8) : Bool := 48 ≤ c && c ≤ 57

/-- Index of the first NUL byte (or the size). -/
def nulIndex (b : ByteArray) : Nat := go 0 b.size
where
  go (i : Nat) : Nat → Nat
    | 0 => i
    | fuel + 1 => if h : i < b.size then (if b[i] == 0 then i else go (i + 1) fuel) else i

/-- The bytes before the first NUL: a C string view. -/
def cstr (b : ByteArray) : ByteArray :=
  let n := nulIndex b
  if n == b.size then b else b.extract 0 n

/-- n copies of byte c. -/
def bytesRepeat (c : UInt8) (n : Nat) : ByteArray :=
  if n == 0 then ByteArray.empty else go (ByteArray.empty.push c) 70
where
  go (r : ByteArray) : Nat → ByteArray
    | 0 => r
    | fuel + 1 => if r.size >= n then r.extract 0 n else go (r ++ r.extract 0 (min r.size (n - r.size))) fuel

/-- Bytes to a String. Invalid UTF-8 (possible only after a byte-precision cut in printf) is read as Latin-1. -/
def bytesToString (b : ByteArray) : String :=
  if h : b.validateUTF8 = true then String.fromUTF8 b (ByteArray.validateUTF8_eq_true_iff.mp h) else
  b.foldl (fun s c => s.push (Char.ofNat c.toNat)) ""

/-! ### 64-bit multiply and powers of ten (util.c) -/

private def aBase : Array UInt64 := #[0x8000000000000000, 0xa000000000000000, 0xc800000000000000, 0xfa00000000000000, 0x9c40000000000000, 0xc350000000000000, 0xf424000000000000, 0x9896800000000000, 0xbebc200000000000, 0xee6b280000000000, 0x9502f90000000000, 0xba43b74000000000, 0xe8d4a51000000000, 0x9184e72a00000000, 0xb5e620f480000000, 0xe35fa931a0000000, 0x8e1bc9bf04000000, 0xb1a2bc2ec5000000, 0xde0b6b3a76400000, 0x8ac7230489e80000, 0xad78ebc5ac620000, 0xd8d726b7177a8000, 0x878678326eac9000, 0xa968163f0a57b400, 0xd3c21bcecceda100, 0x84595161401484a0, 0xa56fa5b99019a5c8]
private def aScale : Array UInt64 := #[0x8049a4ac0c5811ae, 0xcf42894a5dce35ea, 0xa76c582338ed2621, 0x873e4f75e2224e68, 0xda7f5bf590966848, 0xb080392cc4349dec, 0x8e938662882af53e, 0xe65829b3046b0afa, 0xba121a4650e4ddeb, 0x964e858c91ba2655, 0xf2d56790ab41c2a2, 0xc428d05aa4751e4c, 0x9e74d1b791e07e48, 0xcccccccccccccccc, 0xcecb8f27f4200f3a, 0xa70c3c40a64e6c51, 0x86f0ac99b4e8dafd, 0xda01ee641a708de9, 0xb01ae745b101e9e4, 0x8e41ade9fbebc27d, 0xe5d3ef282a242e81, 0xb9a74a0637ce2ee1, 0x95f83d0a1fb69cd9, 0xf24a01a73cf2dccf, 0xc3b8358109e84f07, 0x9e19db92b4e31ba9]
private def aScaleLo : Array UInt32 := #[0x205b896d, 0x52064cad, 0xaf2af2b8, 0x5a7744a7, 0xaf39a475, 0xbd8d794e, 0x547eb47b, 0x0cb4a5a3, 0x92f34d62, 0x3a6a07f9, 0xfae27299, 0xaa97e14c, 0x775ea265, 0xcccccccc, 0x00000000, 0x999090b6, 0x69a028bb, 0xe80e6f48, 0x5ec05dd0, 0x14588f14, 0x8f1668c9, 0x6d953e2c, 0x4abdaf10, 0xbc633b39, 0x0a862f81, 0x6c07a2c2]
private def pow10Tab : Array UInt64 := #[1, 10, 100, 1000, 10000, 100000, 1000000, 10000000, 100000000, 1000000000, 10000000000, 100000000000, 1000000000000, 10000000000000, 100000000000000, 1000000000000000, 10000000000000000, 100000000000000000, 1000000000000000000, 10000000000000000000]

/-- 10^k for k below 20. -/
@[inline] def pow10 (k : Nat) : UInt64 := pow10Tab.getD k 0

/-- Number of decimal digits of v (1 for 0). -/
def numDigits (v : UInt64) : Nat := Id.run do
  let mut k := 1
  for i in [1:20] do
    if v >= pow10 i then k := i + 1
  return k

/-- High 64 bits of the 128-bit product (sqlite3Multiply128). -/
def mulHi (a b : UInt64) : UInt64 :=
  let a0 := a &&& 0xffffffff
  let a1 := a >>> 32
  let b0 := b &&& 0xffffffff
  let b1 := b >>> 32
  let a0b0 := a0 * b0
  let a1b1 := a1 * b1
  let a0b1 := a0 * b1
  let a1b0 := a1 * b0
  let t := (a0b0 >>> 32) + (a0b1 &&& 0xffffffff) + (a1b0 &&& 0xffffffff)
  a1b1 + (a0b1 >>> 32) + (a1b0 >>> 32) + (t >>> 32)

/-- sqlite3Multiply160: top 64 bits and the next 32 bits of (a:aLo) * b. -/
def mul160 (a : UInt64) (aLo : UInt32) (b : UInt64) : UInt64 × UInt32 :=
  let rh := mulHi a b
  let rl := a * b
  let l := aLo.toUInt64
  let w := (mulHi l b <<< 32) ||| ((l * b) >>> 32)
  let rl' := rl + w
  let rh' := if rl' < rl then rh + 1 else rh
  (rh', ((rl' >>> 32) &&& 0xffffffff).toUInt32)

/-- pow10to2(p) = floor(log2(10^p)) approximately, as in sqlite. -/
@[inline] def pwr10to2 (p : Int) : Int := (p * 108853) >>> 15
@[inline] def pwr2to10 (p : Int) : Int := (p * 78913) >>> 18

/-- The most significant 64 bits of 10^p (normalised) and the next 32 bits; p in [-348, 347]. -/
def powerOfTen (p : Int) : UInt64 × UInt32 :=
  if p == -1 then (aScale.getD 13 0, aScaleLo.getD 13 0)
  else if 0 ≤ p && p < 27 then (aBase.getD p.toNat 0, 0)
  else
    let g := p / 27
    let n := (p % 27).toNat
    let gi := (g + 13).toNat
    let s := aScale.getD gi 0
    if n == 0 then (s, aScaleLo.getD gi 0)
    else
      let (x, lo) := mul160 s (aScaleLo.getD gi 0) (aBase.getD n 0)
      if x &&& ((1 : UInt64) <<< 63) == 0 then
        ((x <<< 1) ||| ((lo >>> 31).toUInt64 &&& 1), (lo <<< 1) ||| 1)
      else (x, lo)

/-- Positive infinity. -/
def posInf : Float := Float.ofBits 0x7ff0000000000000

/-- sqlite3Fp2Convert10: m * 2^e as d * 10^p with about n significant digits in d. -/
def fp2Convert10 (m : UInt64) (e : Int) (n : Nat) : UInt64 × Int :=
  let p : Int := (n : Int) - 1 - pwr2to10 (e + 63)
  let h := mulHi m (powerOfTen p).1
  let d : UInt64 :=
    if n == 18 then
      let h' := h >>> (-(e + pwr10to2 p + 2)).toNat.toUInt64
      (h' + ((h' <<< 1) &&& 2)) >>> 1
    else h >>> (-(e + pwr10to2 p + 1)).toNat.toUInt64
  (d, -p)

/-- sqlite3Fp10Convert2: the double closest to d * 10^p (round to nearest, ties to even). -/
def fp10Convert2 (d : UInt64) (p : Int) : Float :=
  if p < -348 then 0.0
  else if p > 347 then posInf
  else if d == 0 then 0.0
  else
    let b : Int := (d.log2.toNat : Int) + 1
    let lp := pwr10to2 p
    let e0 : Int := 53 - b - lp
    if e0 >= 1130 then 0.0 else
    let e : Int := if e0 > 1074 then 1074 else e0
    let s : UInt64 := (-(e - (64 - b) + lp + 3)).toNat.toUInt64
    let (h0, l0) := powerOfTen p
    let (pwr10h, pwr10l) : UInt64 × UInt32 := if l0 != 0 then (h0 + 1, ~~~l0) else (h0, l0)
    let x := d <<< (64 - b).toNat.toUInt64
    let hi0 := mulHi x pwr10h
    let lo := x * pwr10h
    let mid1 : UInt32 := (lo >>> 32).toUInt32
    let (hi, sticky) : UInt64 × UInt64 :=
      if hi0 &&& (((1 : UInt64) <<< s) - 1) == 0 then
        let mid2 : UInt32 := (mulHi x (pwr10l.toUInt64 <<< 32) >>> 32).toUInt32
        (hi0 - (if mid1 < mid2 then 1 else 0), if mid1 - mid2 > 1 then 1 else 0)
      else (hi0, 1)
    let u0 := (hi >>> s) ||| sticky
    let adj := u0 >= ((1 : UInt64) <<< 55) - 2
    let u : UInt64 := if adj then (u0 >>> 1) ||| (u0 &&& 1) else u0
    let e : Int := if adj then e - 1 else e
    let bit2 : UInt64 := (u >>> 2) &&& 1
    let m : UInt64 := (u + 1 + bit2) >>> 2
    if e <= -972 then posInf else
    let m := if m &&& ((1 : UInt64) <<< 52) != 0 then (m &&& ~~~((1 : UInt64) <<< 52)) ||| ((1075 - e).toNat.toUInt64 <<< 52) else m
    Float.ofBits m

/-! ### Decimal digits of a double (sqlite3FpDecode) -/

/-- Result of sqlite3FpDecode: the significant digits as an integer with n digits (no trailing
zeros), the decimal point after iDP digits. special: 0 none, 1 infinity, 2 NaN. -/
structure FpDecode where
  neg : Bool
  special : UInt8
  digits : UInt64
  n : Nat
  iDP : Int

/-- Digit k (0-based from the left) of the n-digit number v. -/
@[inline] def digitAt (v : UInt64) (n k : Nat) : UInt8 := ((v / pow10 (n - 1 - k)) % 10).toUInt8

/-- The digits as ASCII bytes. -/
def FpDecode.digitBytes (s : FpDecode) : ByteArray := Id.run do
  let mut r := ByteArray.empty
  for k in [0:s.n] do
    r := r.push (digitAt s.digits s.n k + 48)
  return r

private def scanDown (v : UInt64) (n : Nat) (ch : UInt8) : Nat → Nat → Nat
  | jj, 0 => jj
  | jj, fuel + 1 => if jj > 0 && digitAt v n (jj - 1) == ch then scanDown v n ch (jj - 1) fuel else jj

/-- The precision-17 shortening of sqlite3FpDecode (the "!" flag): the smallest precision that still
round-trips to r, or 17. -/
private def reduce17 (r : Float) (v : UInt64) (n : Nat) (iDP ex : Int) : Nat :=
  let z := digitAt v n
  let prefixOf (jj : Nat) : UInt64 := v / pow10 (n - jj)
  if z 15 == 9 && z 14 == 9 then
    let jj := scanDown v n 9 14 16
    let v2 := if jj == 0 then 1 else prefixOf jj + 1
    if r == fp10Convert2 v2 (ex + n - jj) then jj + 1 else 17
  else if iDP >= n || (z 15 == 0 && z 14 == 0 && z 13 == 0) then
    let jj := scanDown v n 0 13 16
    if r == fp10Convert2 (prefixOf jj) (ex + n - jj) then jj + 1 else 17
  else 17

private def stripZeros (q : UInt64) (n : Nat) : Nat → UInt64 × Nat
  | 0 => (q, n)
  | fuel + 1 => if n > 1 && q % 10 == 0 then stripZeros (q / 10) (n - 1) fuel else (q, n)

/-- sqlite3FpDecode(r, iRound, mxRound). -/
def fpDecode (r0 : Float) (iRound0 : Int) (mxRound : Nat) : FpDecode :=
  if r0 == 0.0 then ⟨false, 0, 0, 1, 1⟩ else
  let neg := r0 < 0.0
  let r := if neg then -r0 else r0
  let bits := r.toBits
  let e0 := ((bits >>> 52) &&& 0x7ff).toNat
  if e0 == 0x7ff then ⟨neg, if bits == 0x7ff0000000000000 then 1 else 2, 0, 0, 0⟩ else
  let vm := bits &&& 0x000fffffffffffff
  let (v, e) : UInt64 × Int :=
    if e0 == 0 then
      let nn := 63 - vm.log2
      (vm <<< nn, -1074 - nn.toNat)
    else ((vm <<< 11) ||| ((1 : UInt64) <<< 63), (e0 : Int) - 1086)
  let nq : Nat := if iRound0 <= 0 || iRound0 >= 16 then 18 else (iRound0 + 3).toNat
  let (v1, ex) := fp2Convert10 v e nq
  let n1 := numDigits v1
  let iDP1 : Int := n1 + ex
  let (iRound1, n2, iDP2) : Int × Nat × Int :=
    if iRound0 <= 0 then
      let ir := iDP1 - iRound0
      if ir == 0 && v1 / pow10 (n1 - 1) >= 5 then (1, n1 + 1, iDP1 + 1) else (ir, n1, iDP1)
    else (iRound0, n1, iDP1)
  let (q, n3, iDP3) : UInt64 × Nat × Int :=
    if iRound1 > 0 && (iRound1 < n2 || n2 > mxRound) then
      let ir0 : Nat := (min iRound1 mxRound).toNat
      let ir : Nat := if ir0 == 17 then reduce17 r v1 n2 iDP2 ex else ir0
      let q0 := v1 / pow10 (n2 - ir)
      let nxt := (v1 / pow10 (n2 - ir - 1)) % 10
      let q1 := if nxt >= 5 then q0 + 1 else q0
      if q1 == pow10 ir then (q1, ir + 1, iDP2 + 1) else (q1, ir, iDP2)
    else (v1, n2, iDP2)
  let (q', n') := stripZeros q n3 21
  ⟨neg, 0, q', n', iDP3⟩

/-! ### Float rendering (printf.c etFLOAT / etEXP / etGENERIC) -/

/-- Which of %f, %e, %g. -/
inductive FKind where
  | float | exp | generic
  deriving DecidableEq

/-- printf flags that matter to floating point conversions. prefixCh is '+', ' ' or 0. -/
structure FFlags where
  left : Bool := false
  prefixCh : UInt8 := 0
  alt : Bool := false
  alt2 : Bool := false
  zero : Bool := false
  thousand : Bool := false

/-- n spaces. -/
def spaces (n : Int) : ByteArray := bytesRepeat 32 n.toNat

/-- Pad body with spaces to width (on the right when left-justified). -/
def padField (body : ByteArray) (width : Int) (left : Bool) : ByteArray :=
  let w := width - body.size
  if w > 0 then (if left then body ++ spaces w else spaces w ++ body) else body

private def thousandsInt (dz : ByteArray) (n : Nat) : Nat → Int → ByteArray → Nat → ByteArray × Nat
  | 0, _, o, j => (o, j)
  | fuel + 1, e2, o, j =>
    if e2 < 0 then (o, j) else
    let (c, j') : UInt8 × Nat := if j < n then (byteAt dz j, j + 1) else (48, j)
    let o := o.push c
    let o := if e2 % 3 == 0 && e2 > 1 then o.push 44 else o
    thousandsInt dz n fuel (e2 - 1) o j'

/-- Drop trailing zeros and a bare decimal point (adding one zero back with the "!" flag). -/
private def stripTrailing (o : ByteArray) (alt2 : Bool) : ByteArray :=
  let rec cut (k : Nat) : Nat → Nat
    | 0 => k
    | fuel + 1 => if k > 0 && byteAt o (k - 1) == 48 then cut (k - 1) fuel else k
  let k := cut o.size o.size
  if k > 0 && byteAt o (k - 1) == 46 then
    (if alt2 then (o.extract 0 k).push 48 else o.extract 0 (k - 1))
  else o.extract 0 k

private def renderNormal (kind : FKind) (upper : Bool) (precision2 iRound : Int) (fl : FFlags)
    (width : Int) (s : FpDecode) : ByteArray :=
  let prefixCh : UInt8 :=
    if s.neg then (if fl.alt && fl.prefixCh == 0 && kind == .float && s.iDP <= iRound then 0 else 45)
    else fl.prefixCh
  let exp : Int := s.iDP - 1
  let (isExp, prec, rtz) : Bool × Int × Bool :=
    if kind == .generic then
      let p := precision2 - 1
      if exp < -4 || exp > p then (true, p, !fl.alt) else (false, p - exp, !fl.alt)
    else (kind == .exp, precision2, fl.alt2)
  let e2 : Int := if isExp then 0 else s.iDP - 1
  let flagDp := prec > 0 || fl.alt || fl.alt2
  let dz := s.digitBytes
  let o0 := if prefixCh != 0 then ByteArray.empty.push prefixCh else ByteArray.empty
  let (o1, j, e2a) : ByteArray × Nat × Int :=
    if e2 < 0 then (o0.push 48, 0, e2)
    else if fl.thousand then
      let (o, j) := thousandsInt dz s.n (e2.toNat + 1) e2 o0 0
      (o, j, -1)
    else
      let j := min (e2 + 1).toNat s.n
      let o := o0 ++ dz.extract 0 j
      let e2' : Int := e2 - j
      if e2' >= 0 then (o ++ bytesRepeat 48 (e2' + 1).toNat, j, -1) else (o, j, e2')
  let o2 := if flagDp then o1.push 46 else o1
  let (o3, prec1) : ByteArray × Int :=
    if e2a < -1 && prec > 0 then
      let nn := min (-1 - e2a) prec
      (o2 ++ bytesRepeat 48 nn.toNat, prec - nn)
    else (o2, prec)
  let o4 :=
    if prec1 > 0 then
      let nn : Int := min ((s.n : Int) - j) prec1
      let o := if nn > 0 then o3 ++ dz.extract j (j + nn.toNat) else o3
      let p := if nn > 0 then prec1 - nn else prec1
      if p > 0 && !rtz then o ++ bytesRepeat 48 p.toNat else o
    else o3
  let o5 := if rtz && flagDp then stripTrailing o4 fl.alt2 else o4
  let o6 :=
    if isExp then
      let a := exp.natAbs
      let o := (o5.push (if upper then 69 else 101)).push (if exp < 0 then 45 else 43)
      let (o, a) := if a >= 100 then (o.push (a / 100 + 48).toUInt8, a % 100) else (o, a)
      (o.push (a / 10 + 48).toUInt8).push (a % 10 + 48).toUInt8
    else o5
  if (o6.size : Int) < width then
    let nPad := width - o6.size
    if fl.left then o6 ++ spaces nPad
    else if !fl.zero then spaces nPad ++ o6
    else
      let adj := if prefixCh != 0 then 1 else 0
      o6.extract 0 adj ++ bytesRepeat 48 nPad.toNat ++ o6.extract adj o6.size
  else o6

/-- One %f / %e / %g conversion of printf.c (precision < 0 means the default 6), including the field
width. upper selects E and G. -/
def renderFloat (r : Float) (kind : FKind) (upper : Bool) (precision0 : Int) (fl : FFlags) (width : Int) :
    ByteArray :=
  let precision1 : Int := if precision0 < 0 then 6 else min precision0 100000000
  let precision2 : Int := if kind == .generic && precision1 == 0 then 1 else precision1
  let iRound : Int :=
    match kind with
    | .float => -precision2
    | .generic => precision2
    | .exp => precision2 + 1
  let s0 := fpDecode r iRound (if fl.alt2 then 20 else 16)
  if s0.special == 2 then padField (if fl.zero then "null".toUTF8 else "NaN".toUTF8) width fl.left
  else if s0.special == 1 && !fl.zero then
    let inf := "Inf".toUTF8
    let body :=
      if s0.neg then "-Inf".toUTF8
      else if fl.prefixCh != 0 then (ByteArray.empty.push fl.prefixCh) ++ inf else inf
    padField body width fl.left
  else
    let s := if s0.special == 1 then { s0 with digits := 9, iDP := 1000, n := 1 } else s0
    renderNormal kind upper precision2 iRound fl width s

/-! ### Integers to text -/

private def decDigits : Nat → UInt64 → String → String
  | 0, _, s => s
  | fuel + 1, x, s =>
    if x < 10 then s.push (Char.ofNat (x.toNat + 48))
    else (decDigits fuel (x / 10) s).push (Char.ofNat ((x % 10).toNat + 48))

private def decDigitsB : Nat → UInt64 → ByteArray → ByteArray
  | 0, _, s => s
  | fuel + 1, x, s =>
    if x < 10 then s.push (x.toUInt8 + 48)
    else (decDigitsB fuel (x / 10) s).push ((x % 10).toUInt8 + 48)

/-- sqlite3Int64ToText, Int64 minimum included. -/
def int64ToText (i : Int64) : String :=
  if i < 0 then decDigits 21 (0 - i.toUInt64) "-" else decDigits 21 i.toUInt64 ""

/-- int64ToText as ASCII bytes. -/
def int64ToBytes (i : Int64) : ByteArray :=
  if i < 0 then decDigitsB 21 (0 - i.toUInt64) (ByteArray.empty.push 45) else decDigitsB 21 i.toUInt64 ByteArray.empty

/-- A REAL as text exactly as sqlite renders it: "%!.17g" (vdbeMemRenderNum). Whole numbers below 1e15
take a shortcut: their digits are the integer's digits. -/
def fmtRealBytes (f : Float) : ByteArray :=
  if f == f.floor && f.abs < 1000000000000000.0 then
    if f == 0.0 then "0.0".toUTF8 else (int64ToBytes f.toInt64).append ".0".toUTF8
  else renderFloat f .generic false 17 { alt2 := true } 0

/-- A REAL as text exactly as sqlite renders it: "%!.17g" (vdbeMemRenderNum). -/
def fmtReal (f : Float) : String := bytesToString (fmtRealBytes f)

/-! ### Text to numbers (sqlite3AtoF, sqlite3Atoi64) -/

/-- How much of the input sqlite3AtoF accepted. -/
inductive AtoFKind where
  /-- No prefix of the input is a number (return code 0). -/
  | invalid
  /-- A prefix is a number, followed by other text (return code below 0). -/
  | trailing
  /-- The whole input, apart from surrounding whitespace, is a number (return code above 0). -/
  | whole
  deriving DecidableEq, Repr

/-- Result of sqlite3AtoF. flags is sqlite's mState: 1 digit seen, 2 has a decimal point or exponent
(not an integer), 4 exactly zero, 8 more than about 19 significant digits. -/
structure AtoFResult where
  value : Float
  kind : AtoFKind
  flags : UInt8

/-- sqlite3AtoF's int return code. -/
def AtoFResult.rc (r : AtoFResult) : Int :=
  match r.kind with
  | .invalid => 0
  | .trailing => r.flags.toNat - 16
  | .whole => r.flags.toNat

/-- The whole input is a number. -/
def AtoFResult.isWhole (r : AtoFResult) : Bool := r.kind == .whole

/-- Written as an integer: no decimal point and no exponent. -/
def AtoFResult.isInteger (r : AtoFResult) : Bool := r.flags &&& 2 == 0

private def skipSpaces (b : ByteArray) : Nat → Nat → Nat
  | i, 0 => i
  | i, f + 1 => if isSpace (byteAt b i) then skipSpaces b (i + 1) f else i

private def skipDigits (b : ByteArray) : Nat → Int → Nat → Nat × Int
  | i, d, 0 => (i, d)
  | i, d, f + 1 => if isDigit (byteAt b i) then skipDigits b (i + 1) (d + 1) f else (i, d)

private def atofLimit : UInt64 := (0xffffffffffffffff - 9) / 10

private def intDigits (b : ByteArray) : Nat → Nat → UInt64 → Int → Nat × UInt64 × Int × Bool
  | 0, i, s, d => (i, s, d, false)
  | fuel + 1, i, s, d =>
    let c := byteAt b i
    if isDigit c then
      let s' := s * 10 + (c - 48).toUInt64
      if s' >= atofLimit then
        let (i2, d2) := skipDigits b (i + 1) d fuel
        (i2, s', d2, true)
      else intDigits b fuel (i + 1) s' d
    else (i, s, d, false)

private def fracDigits (b : ByteArray) : Nat → Nat → UInt64 → Int → Bool → Nat × UInt64 × Int × Bool
  | 0, i, s, d, sat => (i, s, d, sat)
  | fuel + 1, i, s, d, sat =>
    let c := byteAt b i
    if isDigit c then
      if s < atofLimit then fracDigits b fuel (i + 1) (s * 10 + (c - 48).toUInt64) (d - 1) sat
      else fracDigits b fuel (i + 1) s d true
    else (i, s, d, sat)

private def expDigits (b : ByteArray) : Nat → Nat → UInt64 → Nat × UInt64
  | 0, i, e => (i, e)
  | fuel + 1, i, e =>
    let c := byteAt b i
    if isDigit c then
      let hiBits : UInt64 := e &&& 0xff00000000
      expDigits b fuel (i + 1) (e * 10 + (c - 48).toUInt64 + hiBits)
    else (i, e)

/-- sqlite3AtoF on the bytes of a (C) string: reading stops at the first NUL or the end.
This is the 3.54 behaviour: the text "Inf" is not a number. -/
def atoFBytes (b : ByteArray) : AtoFResult :=
  let n := b.size + 1
  let i0 := skipSpaces b 0 n
  let c0 := byteAt b i0
  -- sign and the integer part
  let (neg, i1) : Bool × Nat :=
    if c0 == 45 then (true, i0 + 1) else if c0 == 43 then (false, i0 + 1) else (false, i0)
  let (i2, s0, d0, fl0) : Nat × UInt64 × Int × UInt8 :=
    if isDigit (byteAt b i1) then
      let (i, s, d, sat) := intDigits b n i1 0 0
      (i, s, d, if sat then 9 else 1)
    else (i1, 0, 0, 0)
  -- the decimal point
  let c2 := byteAt b i2
  if c2 != 46 && fl0 == 0 then ⟨0.0, .invalid, 0⟩ else
  let (i3, s1, d1, fl1) : Nat × UInt64 × Int × UInt8 :=
    if c2 == 46 then
      if isDigit (byteAt b (i2 + 1)) then
        let (i, s, d, sat) := fracDigits b n (i2 + 1) s0 d0 false
        (i, s, d, (if sat then 11 else fl0 ||| 1) ||| 2)
      else (i2 + 1, s0, d0, fl0 ||| 2)
    else (i2, s0, d0, fl0)
  if c2 == 46 && !isDigit (byteAt b (i2 + 1)) && fl0 == 0 then ⟨0.0, .invalid, 0⟩ else
  -- the exponent
  let (i4, d2, fl2) : Nat × Int × UInt8 :=
    let c3 := byteAt b i3
    if c3 == 101 || c3 == 69 then
      let cs := byteAt b (i3 + 1)
      let (esign, j) : Int × Nat := if cs == 45 then (-1, i3 + 2) else if cs == 43 then (1, i3 + 2) else (1, i3 + 1)
      if isDigit (byteAt b j) then
        let (k, e) := expDigits b n (j + 1) (byteAt b j - 48).toUInt64
        (k, d1 + esign * ((e &&& 0xffffffffffff).toNat : Int), fl1 ||| 2)
      else (j - 1, d1, fl1)
    else (i3, d1, fl1)
  -- the value
  let (v, fl3) : Float × UInt8 :=
    if s1 == 0 then (0.0, fl2 ||| 4) else (fp10Convert2 s1 d2, fl2)
  let v := if neg then -v else v
  let i5 := if byteAt b i4 == 0 then i4 else skipSpaces b i4 n
  if byteAt b i5 == 0 then ⟨v, .whole, fl3⟩ else ⟨v, .trailing, fl3⟩

/-- sqlite3AtoF: the value of the longest numeric prefix (0.0 when there is none) and how the parse ended. -/
def atoF (s : String) : AtoFResult := atoFBytes s.toUTF8

/-- Result of sqlite3Atoi64: the (saturated) value and the return code:
-1 no digits at all, 0 the whole text is an integer that fits, 1 an integer followed by other text,
2 too large (value saturated), 3 exactly 9223372036854775808 (value saturated). -/
structure Atoi64Result where
  value : Int64
  rc : Int

private def skipZeros (b : ByteArray) : Nat → Nat → Nat
  | i, 0 => i
  | i, f + 1 => if i < b.size && byteAt b i == 48 then skipZeros b (i + 1) f else i

private def skipSp (b : ByteArray) : Nat → Nat → Nat
  | i, 0 => i
  | i, f + 1 => if i < b.size && isSpace (byteAt b i) then skipSp b (i + 1) f else i

private def accDigits (b : ByteArray) : Nat → Nat → UInt64 → Nat × UInt64
  | 0, i, u => (i, u)
  | f + 1, i, u =>
    if i < b.size && isDigit (byteAt b i) then accDigits b f (i + 1) (u * 10 + (byteAt b i - 48).toUInt64)
    else (i, u)

private def allSpaces (b : ByteArray) : Nat → Nat → Bool
  | _, 0 => true
  | i, f + 1 => if i < b.size then (isSpace (byteAt b i) && allSpaces b (i + 1) f) else true

/-- Compare the 19 digits at i with 9223372036854775808. -/
private def cmp2pow63 (b : ByteArray) (i : Nat) : Ordering :=
  let pow63 := "9223372036854775808".toUTF8
  let rec go (k : Nat) : Nat → Ordering
    | 0 => .eq
    | f + 1 =>
      let x := byteAt b (i + k)
      let y := byteAt pow63 k
      if x < y then .lt else if x > y then .gt else go (k + 1) f
  go 0 19

/-- sqlite3Atoi64 on bytes (length based: NUL bytes are not special). -/
def atoi64Bytes (b : ByteArray) : Atoi64Result :=
  let n := b.size
  let i0 := skipSp b 0 n
  let c0 := byteAt b i0
  let (neg, i1) : Bool × Nat :=
    if i0 < n && c0 == 45 then (true, i0 + 1) else if i0 < n && c0 == 43 then (false, i0 + 1) else (false, i0)
  let i2 := skipZeros b i1 n
  let (i3, u) := accDigits b n i2 0
  let cnt := i3 - i2
  let val : Int64 :=
    if u > 0x7fffffffffffffff then (if neg then Int64.minValue else Int64.maxValue)
    else if neg then -(u.toInt64) else u.toInt64
  let rc0 : Int :=
    if cnt == 0 && i1 == i2 then -1
    else if i3 < n && !allSpaces b i3 n then 1 else 0
  if cnt < 19 then ⟨val, rc0⟩ else
  let j : Ordering := if cnt > 19 then .gt else cmp2pow63 b i2
  if j == .lt then ⟨val, rc0⟩
  else
    let sat := if neg then Int64.minValue else Int64.maxValue
    if j == .gt then ⟨sat, 2⟩ else ⟨sat, if neg then rc0 else 3⟩

/-- sqlite3Atoi64 on text. -/
def atoi64 (s : String) : Atoi64Result := atoi64Bytes s.toUTF8

/-! ### Numeric conversions of values -/

/-- sqlite3RealToI64: saturating truncation. -/
def realToI64 (r : Float) : Int64 :=
  if r < -9223372036854774784.0 then Int64.minValue
  else if r > 9223372036854774784.0 then Int64.maxValue
  else r.toInt64

/-- sqlite3RealSameAsInt: r is exactly the small integer i. -/
def realSameAsInt (r : Float) (i : Int64) : Bool :=
  r == 0.0 || (r.toBits == i.toFloat.toBits && i >= -2251799813685248 && i < 2251799813685248)

/-- sqlite3VdbeIntegerAffinity(bFromText = 1): a REAL that read from text becomes an INTEGER when
that loses nothing (not the extreme integers; as in 3.54, negative zero becomes 0). -/
def integerAffinityFromText (r : Float) : Value :=
  let ix := realToI64 r
  if r == ix.toFloat && ix < Int64.maxValue && ix > Int64.minValue then .int ix
  else .real r

/-- What NUMERIC, INTEGER and REAL column affinity do to a TEXT value (applyNumericAffinity with
bTryForInt = 1) given as bytes: some number when the whole text, apart from surrounding whitespace, is
a well-formed number, none when the text stays text. -/
def bytesToNumeric? (b : ByteArray) : Option Value :=
  let a := atoFBytes b
  if a.kind != .whole then none
  else if a.isInteger then
    let iv := realToI64 a.value
    if realSameAsInt a.value iv then some (.int iv)
    else
      let r := atoi64Bytes b
      if r.rc == 0 then some (.int r.value) else some (integerAffinityFromText a.value)
  else some (integerAffinityFromText a.value)

/-- NUMERIC/INTEGER affinity on text: '12' and ' 7 ' and '1e2' and '3.0' become integers, '3.5' a real,
'0x10' and 'abc' stay text (none). -/
def textToNumeric? (s : String) : Option Value := bytesToNumeric? s.toUTF8

/-- REAL affinity on text: the number as a double. -/
def textToReal? (s : String) : Option Float :=
  (textToNumeric? s).map fun
    | .int i => i.toFloat
    | .real f => f
    | _ => 0.0

/-- A value's bytes as sqlite3_value_text sees them (none for NULL). Numbers are rendered as text. -/
def valueBytes : Value → Option ByteArray
  | .null => none
  | .int i => some (int64ToBytes i)
  | .real f => some (fmtRealBytes f)
  | .text s => some s.toUTF8
  | .blob b => some b

/-- CAST(v AS INTEGER) / sqlite3VdbeIntValue: reals saturate and truncate, text and blobs use the
integer prefix (sqlite3Atoi64: '12abc' is 12, '1e3' is 1). NULL is 0. -/
def castToInt : Value → Int64
  | .null => 0
  | .int i => i
  | .real f => realToI64 f
  | .text s => (atoi64Bytes s.toUTF8).value
  | .blob b => (atoi64Bytes b).value

/-- CAST(v AS REAL) / sqlite3VdbeRealValue: text and blobs use the longest numeric prefix. NULL is 0.0. -/
def castToReal : Value → Float
  | .null => 0.0
  | .int i => i.toFloat
  | .real f => f
  | .text s => (atoFBytes s.toUTF8).value
  | .blob b => (atoFBytes b).value

/-- sqlite3VdbeMemNumerify on text or blob bytes (CAST AS NUMERIC): INTEGER when the prefix is an
integer that fits or the real is a small whole number, else REAL. -/
def numerifyBytes (b : ByteArray) : Value :=
  let a := atoFBytes b
  let ai := atoi64Bytes b
  if (a.isInteger && ai.rc < 2) || realSameAsInt a.value (realToI64 a.value) then
    .int (if a.isInteger && ai.rc < 2 then ai.value else realToI64 a.value)
  else .real a.value

/-- CAST(v AS NUMERIC). NULL stays NULL. -/
def castToNumeric : Value → Value
  | .null => .null
  | .int i => .int i
  | .real f => .real f
  | .text s => numerifyBytes s.toUTF8
  | .blob b => numerifyBytes b

/-- computeNumericType: the number a text or blob has in arithmetic (a well-formed integer that fits
is an INTEGER, anything with a point or exponent is REAL, unparsable text is the integer 0). -/
def arithBytes (b : ByteArray) : Value :=
  let a := atoFBytes b
  if a.isInteger then
    let ai := atoi64Bytes b
    if (if a.kind == .whole then ai.rc == 0 else ai.rc <= 1) then .int ai.value else .real a.value
  else .real a.value

/-- The number a value is in arithmetic (OP_Add and friends): text '12abc' is 12, 'abc' is 0, '1.5x' is
1.5, '3.0' is the REAL 3.0, blobs are read as text; INTEGER and REAL are unchanged and NULL stays NULL. -/
def numericValue : Value → Value
  | .null => .null
  | .int i => .int i
  | .real f => .real f
  | .text s => arithBytes s.toUTF8
  | .blob b => arithBytes b

/-- sqlite3IntFloatCompare: exact comparison of an integer with a (non-NaN) real. -/
def compareIntReal (i : Int64) (r : Float) : Ordering :=
  if r < -9223372036854775808.0 then .gt
  else if r >= 9223372036854775808.0 then .lt
  else
    let y := r.toInt64
    if i < y then .lt else if i > y then .gt else
    let fi := i.toFloat
    if fi < r then .lt else if fi > r then .gt else .eq

/-! ### Integer arithmetic (OP_Add, OP_Subtract, OP_Multiply, OP_Divide, OP_Remainder) -/

/-- a + b, none on overflow (the VDBE then adds as REAL). -/
def addInt? (a b : Int64) : Option Int64 :=
  let r := a + b
  if ((a ^^^ r) &&& (b ^^^ r)) < 0 then none else some r

/-- a - b, none on overflow (the VDBE then subtracts as REAL). -/
def subInt? (a b : Int64) : Option Int64 :=
  let r := a - b
  if ((a ^^^ b) &&& (a ^^^ r)) < 0 then none else some r

/-- a * b, none on overflow (the VDBE then multiplies as REAL). -/
def mulInt? (a b : Int64) : Option Int64 :=
  if a == 0 || b == 0 then some 0
  else if (a == -1 && b == Int64.minValue) || (b == -1 && a == Int64.minValue) then none
  else
    let r := a * b
    if r / b != a then none else some r

/-- a / b truncating toward zero. none in two cases the caller tells apart by testing b: b = 0 gives NULL
(arithmetic_result_is_null); Int64 minimum / -1 overflows and the VDBE then divides as REAL (the REAL
quotient 9.2233720368547758e+18). -/
def divInt? (a b : Int64) : Option Int64 :=
  if b == 0 then none
  else if a == Int64.minValue && b == -1 then none
  else some (a / b)

/-- a % b with the sign of a (C semantics). none only for b = 0 (NULL); b = -1 gives 0 (sqlite maps the
divisor -1 to 1 to dodge the overflow). -/
def remInt? (a b : Int64) : Option Int64 :=
  if b == 0 then none
  else if b == -1 then some 0
  else some (a % b)

/-! ### round() -/

/-- func.c roundFunc on a non-NULL x: n is clamped to 0..30. Values beyond 2^52 have no fraction and are
returned unchanged; n = 0 adds or subtracts 0.5 and truncates (so 0.49999999999999994 rounds to 1.0,
as sqlite 3.54 does); otherwise x is rendered with "%#!.*f" and read back with sqlite3AtoF. -/
def roundReal (x : Float) (n : Int) : Float :=
  let n := if n > 30 then 30 else if n < 0 then 0 else n
  if x < -4503599627370496.0 || x > 4503599627370496.0 then x
  else if n == 0 then (if x >= 0.0 then (x + 0.5).toInt64.toFloat else (x - 0.5).toInt64.toFloat)
  else (atoFBytes (renderFloat x .float false n { alt2 := true } 0)).value

/-! ### The SQL printf() function (printf.c, with the SQLITE_PRINTF_SQLFUNC argument list) -/

/-- Parsed flags, width and precision of one % conversion. -/
structure Spec where
  left : Bool := false
  prefixCh : UInt8 := 0
  alt : Bool := false
  alt2 : Bool := false
  zero : Bool := false
  thousand : Bool := false
  width : Int := 0
  prec : Int := -1

private structure Parsed where
  sp : Spec
  c : UInt8
  pos : Nat
  used : Nat

/-- getIntArg: the next argument as an integer (0 when exhausted). -/
private def argInt (args : Array Value) (used : Nat) : Int64 × Nat :=
  if h : used < args.size then (castToInt args[used], used + 1) else (0, used)

/-- getDoubleArg. -/
private def argReal (args : Array Value) (used : Nat) : Float × Nat :=
  if h : used < args.size then (castToReal args[used], used + 1) else (0.0, used)

/-- getTextArg: the next argument as a C string (none for NULL or when exhausted). -/
private def argText (args : Array Value) (used : Nat) : Option ByteArray × Nat :=
  if h : used < args.size then ((valueBytes args[used]).map cstr, used + 1) else (none, used)

private def parseNum (f : ByteArray) : Nat → Nat → UInt32 → Nat × UInt32
  | 0, i, x => (i, x)
  | fuel + 1, i, x =>
    let c := byteAt f i
    if isDigit c then parseNum f fuel (i + 1) (x * 10 + (c - 48).toUInt32) else (i, x)

/-- The flag, width and precision loop of sqlite3_str_vappendf. pos indexes the current character. -/
private def flagLoop (f : ByteArray) (args : Array Value) : Nat → Nat → Spec → Nat → Parsed
  | 0, pos, sp, used => ⟨sp, byteAt f pos, pos, used⟩
  | fuel + 1, pos, sp, used =>
    let c := byteAt f pos
    let next (sp : Spec) : Parsed :=
      if pos + 1 >= f.size then ⟨sp, 0, pos + 1, used⟩ else flagLoop f args fuel (pos + 1) sp used
    if c == 45 then next { sp with left := true }
    else if c == 43 then next { sp with prefixCh := 43 }
    else if c == 32 then next { sp with prefixCh := 32 }
    else if c == 35 then next { sp with alt := true }
    else if c == 33 then next { sp with alt2 := true }
    else if c == 48 then next { sp with zero := true }
    else if c == 44 then next { sp with thousand := true }
    else if c == 108 then
      if byteAt f (pos + 1) == 108 then ⟨sp, byteAt f (pos + 2), pos + 2, used⟩
      else ⟨sp, byteAt f (pos + 1), pos + 1, used⟩
    else if 49 ≤ c && c ≤ 57 then
      let (q, wx) := parseNum f (f.size + 1) pos 0
      let w : Int := ((wx &&& 0x7fffffff).toNat : Int)
      let sp := { sp with width := w }
      let c' := byteAt f q
      if c' == 46 || c' == 108 then flagLoop f args fuel q sp used else ⟨sp, c', q, used⟩
    else if c == 42 then
      let (v, used') := argInt args used
      let w : Int := v.toInt32.toInt
      let sp := if w < 0 then { sp with left := true, width := if w >= -2147483647 then -w else 0 }
                else { sp with width := w }
      let c1 := byteAt f (pos + 1)
      if c1 != 46 && c1 != 108 then ⟨sp, c1, pos + 1, used'⟩ else flagLoop f args fuel (pos + 1) sp used'
    else if c == 46 then
      let c1 := byteAt f (pos + 1)
      let (sp, q, used') : Spec × Nat × Nat :=
        if c1 == 42 then
          let (v, u') := argInt args used
          let p : Int := v.toInt32.toInt
          let p := if p < 0 then (if p >= -2147483647 then -p else -1) else p
          ({ sp with prec := p }, pos + 2, u')
        else
          let (q, px) := parseNum f (f.size + 1) (pos + 1) 0
          ({ sp with prec := ((px &&& 0x7fffffff).toNat : Int) }, q, used)
      let c' := byteAt f q
      if c' == 108 then flagLoop f args fuel q sp used' else ⟨sp, c', q, used'⟩
    else ⟨sp, c, pos, used⟩

/-- Longest string sqlite builds (SQLITE_MAX_LENGTH): beyond it printf() raises "string or blob too big". -/
def maxLength : Nat := 1000000000

private inductive Step where
  | fail
  | stop
  | ok (out : ByteArray) (used : Nat)

private def repeatBytes (b : ByteArray) (n : Nat) : ByteArray :=
  if n == 0 || b.size == 0 then ByteArray.empty else go b 70
where
  go (r : ByteArray) : Nat → ByteArray
    | 0 => r
    | fuel + 1 =>
      if r.size >= b.size * n then r else go (r ++ r.extract 0 (min r.size (b.size * n - r.size))) fuel

private def contCount (b : ByteArray) : Nat := b.foldl (fun n c => if c &&& 0xc0 == 0x80 then n + 1 else n) 0

private def radixDigits (base : UInt64) (upper : Bool) : Nat → UInt64 → ByteArray → ByteArray
  | 0, _, acc => acc
  | fuel + 1, x, acc =>
    let dig (d : UInt64) : UInt8 :=
      if d < 10 then d.toUInt8 + 48 else d.toUInt8 + (if upper then 55 else 87)
    if x < base then acc.push (dig x)
    else (radixDigits base upper fuel (x / base) acc).push (dig (x % base))

private def addCommas (b : ByteArray) : ByteArray := Id.run do
  let l := b.size
  let mut r := ByteArray.empty
  for k in [0:l] do
    if k > 0 && (l - k) % 3 == 0 then r := r.push 44
    r := r.push (byteAt b k)
  return r

/-- %d %i %u %x %X %o %p %r. -/
private def intConv (sp : Spec) (c : UInt8) (v : Int64) : ByteArray :=
  let signed := c == 100 || c == 105 || c == 114
  let base : UInt64 := if c == 111 then 8 else if c == 120 || c == 88 || c == 112 then 16 else 10
  let upper := c == 88 || c == 112
  let preKind : Nat := if c == 120 || c == 112 then 1 else if c == 111 then 2 else if c == 88 then 3 else 0
  let thousandOk := c == 100 || c == 105 || c == 117
  let (lv, pfx) : UInt64 × UInt8 :=
    if signed then (if v < 0 then (~~~v.toUInt64 + 1, 45) else (v.toUInt64, sp.prefixCh)) else (v.toUInt64, 0)
  let alt := sp.alt && lv != 0
  let pf : Int := if pfx != 0 then 1 else 0
  let (width, prec) : Int × Int :=
    if sp.zero then
      (sp.width, if sp.prec < sp.width - pf then sp.width - pf else sp.prec)
    else (sp.width, sp.prec)
  let digs := radixDigits base upper 70 lv ByteArray.empty
  let body0 :=
    if c == 114 then
      let x := (lv % 10).toNat
      let x := if x >= 4 || (lv / 10) % 10 == 1 then 0 else x
      digs ++ ("thstndrd".toUTF8.extract (x * 2) (x * 2 + 2))
    else digs
  let body1 := if prec > body0.size then bytesRepeat 48 (prec - body0.size).toNat ++ body0 else body0
  let body2 := if thousandOk && sp.thousand then addCommas body1 else body1
  let body3 := if pfx != 0 then (ByteArray.empty.push pfx) ++ body2 else body2
  let body4 :=
    if alt && preKind != 0 then
      (if preKind == 2 then "0".toUTF8 else if preKind == 1 then "0x".toUTF8 else "0X".toUTF8) ++ body3
    else body3
  padField body4 width sp.left

/-- %c: the first character of the text argument, repeated precision times. -/
private def charConv (sp : Spec) (t : Option ByteArray) (out : ByteArray) : ByteArray :=
  let buf : ByteArray :=
    match t with
    | none => ByteArray.empty.push 0
    | some t =>
      if t.size == 0 then ByteArray.empty.push 0
      else if byteAt t 0 &&& 0xc0 == 0xc0 then
        let k := (List.range 3).foldl (fun k i => if k == i + 1 && (byteAt t k &&& 0xc0) == 0x80 then k + 1 else k) 1
        t.extract 0 k
      else t.extract 0 1
  let (out1, width1) : ByteArray × Int :=
    if sp.prec > 1 then
      let w := sp.width - (sp.prec - 1)
      let (outA, wB) : ByteArray × Int := if w > 1 && !sp.left then (out ++ spaces (w - 1), 0) else (out, w)
      (outA ++ repeatBytes buf (sp.prec - 1).toNat, wB)
    else (out, sp.width)
  let width2 := if width1 > 0 then width1 + contCount buf else width1
  out1 ++ padField buf width2 sp.left

private def utf8Take (b : ByteArray) : Nat → Nat → Nat → Nat
  | _, z, 0 => z
  | k, z, fuel + 1 =>
    if k == 0 || z >= b.size then z
    else
      let c := byteAt b z
      let z' := z + 1
      let z'' := if c >= 0xc0 then skipCont b z' (b.size + 1) else z'
      utf8Take b (k - 1) z'' fuel
where
  skipCont (b : ByteArray) (z : Nat) : Nat → Nat
    | 0 => z
    | f + 1 => if z < b.size && (byteAt b z &&& 0xc0) == 0x80 then skipCont b (z + 1) f else z

/-- %s %z. -/
private def strConv (sp : Spec) (t : Option ByteArray) : ByteArray :=
  let bytes := t.getD ByteArray.empty
  let len : Nat :=
    if sp.prec >= 0 then
      (if sp.alt2 then utf8Take bytes sp.prec.toNat 0 (bytes.size + 1) else min sp.prec.toNat bytes.size)
    else bytes.size
  let body := bytes.extract 0 len
  let width := if sp.alt2 && sp.width > 0 then sp.width + contCount body else sp.width
  padField body width sp.left

private def escScan (esc : ByteArray) (q : UInt8) (alt2 : Bool) : Nat → Int → Nat → Nat
  | i, _, 0 => i
  | i, k, fuel + 1 =>
    if k == 0 || i >= esc.size then i
    else
      let ch := byteAt esc i
      let i' := if alt2 && ch &&& 0xc0 == 0xc0 then utf8Take.skipCont esc (i + 1) (esc.size + 1) - 1 else i
      escScan esc q alt2 (i' + 1) (k - 1) fuel

/-- %q %Q %w. -/
private def escConv (sp : Spec) (c : UInt8) (t : Option ByteArray) : ByteArray :=
  let isQ := c == 81
  let isW := c == 119
  let (esc, needQuote0) : ByteArray × Nat :=
    match t with
    | none => ((if isQ then "NULL" else "(NULL)").toUTF8, 0)
    | some t => (t, if isQ then 1 else 0)
  let q : UInt8 := if isW then 34 else 39
  let alt0 := if isW then false else sp.alt
  let i := escScan esc q sp.alt2 0 sp.prec (esc.size + 1)
  let nCtrl := (esc.extract 0 i).foldl (fun n ch => if ch != 92 && ch <= 0x1f then n + 1 else n) 0
  let (alt, needQuote) : Bool × Nat :=
    if alt0 then
      (if nCtrl > 0 || c == 113 then (true, if isQ then 2 else needQuote0) else (false, needQuote0))
    else (false, needQuote0)
  let o0 : ByteArray :=
    if needQuote == 2 then "unistr('".toUTF8 else if needQuote == 1 then "'".toUTF8 else ByteArray.empty
  let hex (x : UInt8) : UInt8 := if x < 10 then x + 48 else x + 87
  let body := Id.run do
    let mut o := o0
    for k in [0:i] do
      let ch := byteAt esc k
      if alt then
        if ch == q then o := (o.push ch).push ch
        else if ch == 92 then o := (o.push 92).push 92
        else if ch <= 0x1f then
          o := ((((o.push 92).push 117).push 48).push 48).push (if ch >= 0x10 then 49 else 48) |>.push (hex (ch &&& 15))
        else o := o.push ch
      else
        o := if ch == q then (o.push ch).push ch else o.push ch
    return o
  let body := if needQuote != 0 then (body.push 39) else body
  let body := if needQuote == 2 then body.push 41 else body
  let width := if sp.alt2 && sp.width > 0 then sp.width + contCount body else sp.width
  padField body width sp.left

private def jsonScan (esc : ByteArray) : Nat → Nat → Nat → Nat × Nat
  | i, px, 0 => (i, px)
  | i, px, f + 1 =>
    if i < px && byteAt esc i != 0 then jsonScan esc (i + 1) (if (byteAt esc i &&& 0xc0) == 0x80 then px + 1 else px) f
    else (i, px)

private def jsonBody (esc : ByteArray) (px : Nat) : Nat → Nat → ByteArray → Nat → ByteArray
  | i, j, acc, 0 => acc ++ esc.extract j i
  | i, j, acc, fuel + 1 =>
    if i >= px then acc ++ esc.extract j (min i esc.size) else
    let ch := byteAt esc i
    if ch <= 0x1f || ch == 34 || ch == 92 then
      let acc := if j < i then acc ++ esc.extract j i else acc
      if ch == 0 then acc else
      let hex (x : UInt8) : UInt8 := if x < 10 then x + 48 else x + 87
      let acc := acc.push 92
      let acc :=
        if ch > 0x1f then acc.push ch
        else if ((1 : UInt32) <<< ch.toUInt32) &&& 0x3700 != 0 then acc.push (byteAt "btn?fr".toUTF8 (ch.toNat - 8))
        else ((((acc.push 117).push 48).push 48).push (hex (ch >>> 4))).push (hex (ch &&& 15))
      jsonBody esc px (i + 1) (i + 1) acc fuel
    else jsonBody esc px (i + 1) j acc fuel

/-- %j %J. -/
private def jsonConv (sp : Spec) (c : UInt8) (t : Option ByteArray) : ByteArray :=
  let isJ := c == 74
  let body : ByteArray :=
    match t with
    | none => if isJ then "null".toUTF8 else ByteArray.empty
    | some esc =>
      let px0 : Nat := if sp.prec < 0 then 0x7fffffff else sp.prec.toNat
      let px : Nat :=
        if sp.prec >= 0 && sp.alt2 then
          let (i, px) := jsonScan esc 0 px0 (esc.size + 2)
          if i == px then utf8Take.skipCont esc px (esc.size + 1) else px
        else px0
      let b := jsonBody esc px 0 0 ByteArray.empty (esc.size + 2)
      if isJ then ((ByteArray.empty.push 34) ++ b).push 34 else b
  let n := body.size
  let len : Int := if sp.alt2 && n > 0 then (n : Int) - contCount body else n
  if sp.width > len then
    (if sp.left then body ++ spaces (sp.width - len) else spaces (sp.width - len) ++ body)
  else body

private def findPercent (f : ByteArray) : Nat → Nat → Nat
  | i, 0 => i
  | i, fuel + 1 => if i < f.size && byteAt f i != 37 then findPercent f (i + 1) fuel else i

private def convert (sp : Spec) (c : UInt8) (args : Array Value) (used : Nat) (out : ByteArray) : Step :=
  let isFloat := c == 101 || c == 69 || c == 102 || c == 103 || c == 71
  let prec := if isFloat then min sp.prec 100000000 else sp.prec
  let big := out.size + sp.width.toNat + (max prec 0).toNat > maxLength
  let isNumeric := c == 100 || c == 105 || c == 117 || c == 120 || c == 88 || c == 111 || c == 112 || c == 114
    || isFloat || c == 99
  if out.size + sp.width.toNat > maxLength || (isNumeric && big) then .fail
  else if c == 100 || c == 105 || c == 117 || c == 120 || c == 88 || c == 111 || c == 112 || c == 114 then
    let (v, u) := argInt args used
    .ok (out ++ intConv sp c v) u
  else if c == 101 || c == 69 || c == 102 || c == 103 || c == 71 then
    let (r, u) := argReal args used
    let kind := if c == 102 then FKind.float else if c == 101 || c == 69 then .exp else .generic
    let fl : FFlags := ⟨sp.left, sp.prefixCh, sp.alt, sp.alt2, sp.zero, sp.thousand⟩
    .ok (out ++ renderFloat r kind (c == 69 || c == 71) sp.prec fl sp.width) u
  else if c == 37 then .ok (out ++ padField "%".toUTF8 sp.width sp.left) used
  else if c == 99 then
    let (t, u) := argText args used
    .ok (charConv sp t out) u
  else if c == 115 || c == 122 then
    let (t, u) := argText args used
    .ok (out ++ strConv sp t) u
  else if c == 113 || c == 81 || c == 119 then
    let (t, u) := argText args used
    .ok (out ++ escConv sp c t) u
  else if c == 106 || c == 74 then
    let (t, u) := argText args used
    .ok (out ++ jsonConv sp c t) u
  else if c == 110 then .ok out used
  else .stop

private def pfLoop (f : ByteArray) (args : Array Value) : Nat → Nat → ByteArray → Nat → Option ByteArray
  | 0, _, out, _ => some out
  | fuel + 1, pos, out, used =>
    if pos >= f.size then some out
    else if byteAt f pos != 37 then
      let e := findPercent f pos f.size
      pfLoop f args fuel e (out ++ f.extract pos e) used
    else if pos + 1 >= f.size then some (out.push 37)
    else
      let p := flagLoop f args (f.size + 2) (pos + 1) {} used
      match convert p.sp p.c args p.used out with
      | .fail => none
      | .stop => some out
      | .ok out' used' => pfLoop f args fuel (p.pos + 1) out' used'

/-- sqlite's printf()/format() SQL function on a format given as bytes: the formatted bytes, or none when
the result would exceed maxLength (sqlite raises "string or blob too big"). Arguments are coerced as
func.c does (integer: Atoi64 prefix or saturating truncation; double: AtoF prefix; text: the value's
text); missing arguments read as 0, 0.0 and NULL. -/
def printfBytes? (fmt : ByteArray) (args : Array Value) : Option ByteArray :=
  let f := cstr fmt
  pfLoop f args (f.size + 1) 0 ByteArray.empty 0

/-- sqlite's printf()/format() SQL function. The result is empty when sqlite would raise "string or blob too
big". A byte-precision cut of a multi-byte character (%.1s without the ! flag) gives bytes that are not
UTF-8; they are read as Latin-1 here (use printfBytes? to see the exact bytes). -/
def printf (fmt : String) (args : List Value) : String :=
  match printfBytes? fmt.toUTF8 args.toArray with
  | some b => bytesToString b
  | none => ""

end LSql.Num

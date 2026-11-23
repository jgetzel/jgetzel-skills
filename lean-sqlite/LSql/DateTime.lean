import LSql.Num
import LSql.Value

/-! sqlite's date and time functions (src/date.c, sqlite 3.54): date, time, datetime, julianday,
unixepoch, strftime, timediff. The arithmetic is date.c's: the instant is a Julian day number in
milliseconds (iJD), converted to and from year/month/day and hour/minute/second exactly as
computeJD, computeYMD and computeHMS do, so results agree with sqlite to the millisecond.

The local time zone is assumed to be UTC: the 'localtime' and 'utc' modifiers convert through UTC. -/

namespace LSql.DateTime

open LSql LSql.Num

/-- date.c's DateTime. -/
structure DT where
  iJD : Int64 := 0
  Y : Int := 0
  M : Int := 0
  D : Int := 0
  h : Int := 0
  m : Int := 0
  tz : Int := 0
  s : Float := 0.0
  validJD : Bool := false
  validYMD : Bool := false
  validHMS : Bool := false
  nFloor : Int := 0
  rawS : Bool := false
  isError : Bool := false
  useSubsec : Bool := false
  isUtc : Bool := false
  isLocal : Bool := false

/-- The julian day number of the Unix epoch, times 86400000. -/
def unixOffsetMs : Int64 := 210866760000000

/-- The largest valid iJD (9999-12-31 23:59:59.999). -/
def maxJD : Int64 := 464269060799999

@[inline] def validJulianDay (iJD : Int64) : Bool := 0 ≤ iJD && iJD ≤ maxJD

@[inline] private def tdiv (a b : Int) : Int := Int.tdiv a b
@[inline] private def i64 (x : Int) : Int64 := Int64.ofInt x
/-- C's (int) cast of a double. -/
@[inline] private def f2i (f : Float) : Int := f.toInt64.toInt
@[inline] private def msDay : Int64 := 86400000

/-! ### Parsing helpers -/

@[inline] def lowerB (c : UInt8) : UInt8 := if 65 ≤ c && c ≤ 90 then c + 32 else c

private def readDigits (b : ByteArray) (i : Nat) : Nat → Nat → Option Nat
  | 0, acc => some acc
  | n + 1, acc =>
    let c := byteAt b i
    if isDigit c then readDigits b (i + 1) n (acc * 10 + (c - 48).toNat) else none

/-- date.c getDigits for one number: n digits at i with value in [lo, hi], followed by the byte sep
(none required when sep is 0). -/
def gd (b : ByteArray) (i n lo hi : Nat) (sep : UInt8) : Option Nat :=
  match readDigits b i n 0 with
  | some v => if v < lo || v > hi || (sep != 0 && byteAt b (i + n) != sep) then none else some v
  | none => none

private def skipWs (b : ByteArray) (i : Nat) : Nat → Nat
  | 0 => i
  | f + 1 => if isSpace (byteAt b i) then skipWs b (i + 1) f else i

/-- Skip whitespace from i. -/
def ws (b : ByteArray) (i : Nat) : Nat := skipWs b i (b.size + 1)

private def skipWsT (b : ByteArray) (i : Nat) : Nat → Nat
  | 0 => i
  | f + 1 => let c := byteAt b i; if isSpace c || c == 84 then skipWsT b (i + 1) f else i

private def icmpFrom (z : ByteArray) (zi : Nat) (l : ByteArray) (j : Nat) : Nat → Bool
  | 0 => true
  | f + 1 => if j < l.size then lowerB (byteAt z (zi + j)) == byteAt l j && icmpFrom z zi l (j + 1) f else true

/-- sqlite3_stricmp against a lower case ASCII literal. -/
def ieq (z : ByteArray) (lit : String) : Bool :=
  let l := lit.toUTF8
  z.size == l.size && icmpFrom z 0 l 0 l.size

/-- sqlite3_strnicmp(z, lit, lit.length) == 0. -/
def startsI (z : ByteArray) (lit : String) : Bool :=
  let l := lit.toUTF8
  z.size ≥ l.size && icmpFrom z 0 l 0 l.size

private def daysOfMonth (Y M : Int) : Int :=
  if (1 <<< M.toNat) &&& 0x15aa != 0 then 31
  else if M != 2 then 30
  else if Int.tmod Y 4 == 0 && (Int.tmod Y 100 != 0 || Int.tmod Y 400 == 0) then 29 else 28

def computeFloor (p : DT) : DT :=
  let mxD := daysOfMonth p.Y p.M
  { p with nFloor := if p.D > mxD then p.D - mxD else 0 }

def datetimeError : DT := { isError := true }

/-- date.c computeJD. -/
def computeJD (p : DT) : DT :=
  if p.validJD then p else
  let (Y, M, D, p) : Int × Int × Int × DT :=
    if p.validYMD then (p.Y, p.M, p.D, p)
    else if p.validHMS && p.h == 24 then (2000, 1, 2, { p with h := 0 })
    else (2000, 1, 1, p)
  if Y < -4713 || Y > 9999 || p.rawS then datetimeError else
  let (Y, M) := if M ≤ 2 then (Y - 1, M + 12) else (Y, M)
  let A := tdiv (Y + 4800) 100
  let B := 38 - A + tdiv A 4
  let X1 := tdiv (36525 * (Y + 4716)) 100
  let X2 := tdiv (306001 * (M + 1)) 10000
  let iJD := Float.toInt64 ((Float.ofInt (X1 + X2 + D + B) - 1524.5) * 86400000.0)
  let p := { p with iJD := iJD, validJD := true }
  if p.validHMS then
    let iJD := p.iJD + i64 (p.h * 3600000 + p.m * 60000) + Float.toInt64 (p.s * 1000.0 + 0.5)
    if p.tz != 0 then
      { p with iJD := iJD - i64 (p.tz * 60000), validYMD := false, validHMS := false, tz := 0,
               isUtc := true, isLocal := false }
    else { p with iJD := iJD }
  else p

/-- date.c computeYMD. -/
def computeYMD (p : DT) : DT :=
  if p.validYMD then p
  else if !p.validJD then { p with Y := 2000, M := 1, D := 1, validYMD := true }
  else if !validJulianDay p.iJD then datetimeError
  else
    let Z : Int := ((p.iJD + 43200000) / msDay).toInt
    let alpha := f2i ((Float.ofInt Z + 32044.75) / 36524.25) - 52
    let A := Z + 1 + alpha - tdiv (alpha + 100) 4 + 25
    let B := A + 1524
    let C := f2i ((Float.ofInt B - 122.1) / 365.25)
    let D := tdiv (36525 * (C % 32768)) 100
    let E := f2i (Float.ofInt (B - D) / 30.6001)
    let X1 := f2i (30.6001 * Float.ofInt E)
    let M := if E < 14 then E - 1 else E - 13
    { p with D := B - D - X1, M := M, Y := if M > 2 then C - 4716 else C - 4715, validYMD := true }

/-- date.c computeHMS. -/
def computeHMS (p : DT) : DT :=
  if p.validHMS then p else
  let p := computeJD p
  let dayMs : Int := ((p.iJD + 43200000) % msDay).toInt
  let dayMin := tdiv dayMs 60000
  { p with s := Float.ofInt (Int.tmod dayMs 60000) / 1000.0, m := Int.tmod dayMin 60, h := tdiv dayMin 60,
           rawS := false, validHMS := true }

def computeYMD_HMS (p : DT) : DT := computeHMS (computeYMD p)

def clearYMD_HMS_TZ (p : DT) : DT := { p with validYMD := false, validHMS := false, tz := 0 }

/-! ### Parsing time values -/

/-- date.c parseTimezone: (+|-)HH:MM or Z, then only whitespace. -/
def parseTimezone (b : ByteArray) (i : Nat) (p : DT) : Option DT :=
  let i := ws b i
  let p := { p with tz := 0 }
  let c := byteAt b i
  let finish (j : Nat) (p : DT) : Option DT := if byteAt b (ws b j) != 0 then none else some p
  if c == 90 || c == 122 then finish (i + 1) { p with isLocal := false, isUtc := true }
  else if c == 45 || c == 43 then
    match gd b (i + 1) 2 0 14 58, gd b (i + 4) 2 0 59 0 with
    | some nHr, some nMn =>
      let sgn : Int := if c == 45 then -1 else 1
      let tz := sgn * ((nMn : Int) + nHr * 60)
      finish (i + 6) (if tz == 0 then { p with tz := tz, isLocal := false, isUtc := true } else { p with tz := tz })
    | _, _ => none
  else if c != 0 then none else some p

private def fracLoop (b : ByteArray) (i : Nat) (ms sc : Float) : Nat → Nat × Float × Float
  | 0 => (i, ms, sc)
  | f + 1 =>
    let c := byteAt b i
    if isDigit c then fracLoop b (i + 1) ((ms * 10.0 + c.toNat.toFloat) - 48.0) (sc * 10.0) f
    else (i, ms, sc)

/-- date.c parseHhMmSs: HH:MM[:SS[.FFF]] at i. -/
def parseHhMmSs (b : ByteArray) (i : Nat) (p : DT) (allowTZ : Bool) : Option DT :=
  match gd b i 2 0 24 58, gd b (i + 3) 2 0 59 0 with
  | some h, some m =>
    let i1 := i + 5
    let r : Option (Nat × Nat × Float) :=
      if byteAt b i1 == 58 then
        match gd b (i1 + 1) 2 0 59 0 with
        | none => none
        | some s =>
          let i2 := i1 + 3
          if byteAt b i2 == 46 && isDigit (byteAt b (i2 + 1)) then
            let (i3, ms, sc) := fracLoop b (i2 + 1) 0.0 1.0 (b.size + 1)
            let ms := ms / sc
            some (s, i3, if ms > 0.999 then 0.999 else ms)
          else some (s, i2, 0.0)
      else some (0, i1, 0.0)
    match r with
    | none => none
    | some (s, i2, ms) =>
      if h == 24 && (m != 0 || s != 0 || ms != 0.0) then none else
      let p := { p with validJD := false, rawS := false, validHMS := true, h := h, m := m, s := s.toFloat + ms }
      if !allowTZ && byteAt b i2 != 0 then none else parseTimezone b i2 p
  | _, _ => none

/-- date.c parseYyyyMmDd. -/
def parseYyyyMmDd (b : ByteArray) (p : DT) : Option DT :=
  let neg := byteAt b 0 == 45
  let i0 := if neg then 1 else 0
  match gd b i0 4 0 14712 45, gd b (i0 + 5) 2 1 12 45, gd b (i0 + 8) 2 1 31 0 with
  | some Y, some M, some D =>
    let Y : Int := if neg then -(Y : Int) else Y
    let i := skipWsT b (i0 + 10) (b.size + 1)
    let r : Option (DT × Int × Int × Int) :=
      match parseHhMmSs b i p true with
      | some p' =>
        if p'.h == 24 then
          let mxD := daysOfMonth Y M
          let D := (D : Int) + 1
          let (Y, M, D) := if D > mxD then (if M + 1 > 12 then (Y + 1, (1 : Int), D - mxD) else (Y, (M : Int) + 1, D - mxD))
                           else (Y, (M : Int), D)
          some ({ p' with h := 0 }, Y, M, D)
        else some (p', Y, M, D)
      | none => if byteAt b i == 0 then some ({ p with validHMS := false }, Y, M, D) else none
    match r with
    | none => none
    | some (p, Y, M, D) =>
      let p := computeFloor { p with validJD := false, validYMD := true, Y := Y, M := M, D := D }
      some (if p.tz != 0 then computeJD p else p)
  | _, _, _ => none

/-- date.c setDateTimeToCurrent. -/
def setCurrent (now : Option Int64) (p : DT) : Option DT :=
  match now with
  | none => none
  | some ms =>
    let iJD := ms + unixOffsetMs
    if iJD > 0 then
      some (clearYMD_HMS_TZ { p with iJD := iJD, validJD := true, isUtc := true, isLocal := false })
    else none

/-- date.c setRawDateNumber. -/
def setRaw (p : DT) (r : Float) : DT :=
  let p := { p with s := r, rawS := true }
  if r ≥ 0.0 && r < 5373484.5 then { p with iJD := Float.toInt64 (r * 86400000.0 + 0.5), validJD := true } else p

/-- date.c parseDateOrTime on a C string. -/
def parseDateOrTime (b : ByteArray) (now : Option Int64) (p : DT) : Option DT :=
  match parseYyyyMmDd b p with
  | some p => some p
  | none =>
  match parseHhMmSs b 0 p true with
  | some p => some p
  | none =>
  if ieq b "now" then setCurrent now p
  else if (atoFBytes b).rc > 0 then some (setRaw p (atoFBytes b).value)
  else if ieq b "subsec" || ieq b "subsecond" then setCurrent now { p with useSubsec := true }
  else none

/-! ### Local time (the local zone is UTC) -/

/-- The proleptic Gregorian date of a day count since 1970-01-01. -/
def civilFromDays (z : Int) : Int × Int × Int :=
  let z := z + 719468
  let era := z / 146097
  let doe := z - era * 146097
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
  let mp := (5 * doy + 2) / 153
  let d := doy - (153 * mp + 2) / 5 + 1
  let m := if mp < 10 then mp + 3 else mp - 9
  (yoe + era * 400 + (if m ≤ 2 then 1 else 0), m, d)

/-- date.c toLocaltime with the local zone fixed to UTC (gmtime in place of localtime_r). -/
def toLocaltime (p : DT) : DT :=
  let p := computeJD p
  let (t, yearDiff) : Int × Int :=
    if p.iJD < 210866760000000 || p.iJD > 213014145600000 then
      let x := computeYMD_HMS p
      let diff := (2000 + Int.tmod x.Y 4) - x.Y
      let x := computeJD { x with Y := x.Y + diff, validJD := false }
      ((x.iJD / 1000).toInt - 210866760000, diff)
    else ((p.iJD / 1000).toInt - 210866760000, 0)
  let days := t / 86400
  let secs := t % 86400
  let (Y, M, D) := civilFromDays days
  { p with Y := Y - yearDiff, M := M, D := D, h := secs / 3600, m := secs % 3600 / 60,
           s := Float.ofInt (secs % 60) + Float.ofInt (p.iJD % 1000).toInt * 0.001,
           validYMD := true, validHMS := true, validJD := false, rawS := false, tz := 0, isError := false }

private def utcLoop (orig guess err : Int64) : Nat → Int64
  | 0 => guess
  | n + 1 =>
    let guess := guess - err
    let nw := computeJD (toLocaltime { iJD := guess, validJD := true })
    let err := nw.iJD - orig
    if err != 0 then utcLoop orig guess err n else guess

/-! ### Modifiers -/

/-- date.c aXformType: name, (float) limit, (float) multiplier. -/
private def xforms : Array (String × Float × Float) :=
  #[("second", (4.6427e+14 : Float32).toFloat, 1.0), ("minute", (7.7379e+12 : Float32).toFloat, 60.0),
    ("hour", (1.2897e+11 : Float32).toFloat, 3600.0), ("day", 5373485.0, 86400.0),
    ("month", 176546.0, 2592000.0), ("year", 14713.0, 31536000.0)]

private def xformIdx (z : ByteArray) (n : Nat) (r : Float) (i : Nat) : Nat → Option Nat
  | 0 => none
  | f + 1 =>
    match xforms[i]? with
    | none => none
    | some (name, lim, _) =>
      if name.length == n && icmpFrom z 0 name.toUTF8 0 n && r > -lim && r < lim then some i
      else xformIdx z n r (i + 1) f

private def hasByte (z : ByteArray) (c : UInt8) (i : Nat) : Nat → Bool
  | 0 => false
  | f + 1 => i < z.size && (z[i]? == some c || hasByte z c (i + 1) f)

private def numEnd (z : ByteArray) : Nat → Nat → Nat
  | n, 0 => n
  | n, f + 1 =>
    let c := byteAt z n
    if c == 0 || c == 58 || isSpace c then n
    else if c == 45 && ((n == 5 && (gd z 1 4 0 14712 0).isSome) || (n == 6 && (gd z 1 5 0 14712 0).isSome)) then n
    else numEnd z (n + 1) f

/-- The "HH:MM[:SS.FFF]" shift; z2 is where the time starts. As in the sqlite3 3.54.0 binary (not the 3.55 development
source), a time zone suffix is accepted, 24:00 shifts by nothing and the shift leaves nFloor alone. -/
private def timeShift (z : ByteArray) (z2 : Nat) (z0 : UInt8) (p : DT) : Option DT :=
  let z2 := if isDigit (byteAt z z2) then z2 else z2 + 1
  match parseHhMmSs z z2 {} true with
  | none => none
  | some tx =>
    let tx := computeJD tx
    let tiJD := tx.iJD - 43200000
    let day := tiJD / msDay
    let tiJD := tiJD - day * msDay
    let tiJD := if z0 == 45 then -tiJD else tiJD
    let p := clearYMD_HMS_TZ (computeJD p)
    some { p with iJD := p.iJD + tiJD }

/-- The modifiers that begin with a sign or digit: NNN unit, (+|-)HH:MM:SS.SSS, (+|-)YYYY-MM-DD [HH:MM...]. -/
private def numericMod (z : ByteArray) (p : DT) : Option DT :=
  let z0 := byteAt z 0
  let n := numEnd z 1 (z.size + 1)
  let ar := atoFBytes (z.extract 0 n)
  if ar.rc ≤ 0 then none else
  let r := ar.value
  let unitForm (p : DT) : Option DT :=
    let st := ws z n
    let rest := z.extract st z.size
    let len := rest.size
    if len < 3 || len > 10 then none else
    let len := if lowerB (byteAt rest (len - 1)) == 115 then len - 1 else len
    let p := { computeJD p with nFloor := 0 }
    let rRounder : Float := if r < 0.0 then -0.5 else 0.5
    match xformIdx rest len r 0 6 with
    | none => none
    | some i =>
      let xf := (xforms[i]?.map (·.2.2)).getD 1.0
      let (p, r) : DT × Float :=
        if i == 4 then
          let p := computeYMD_HMS p
          let M := p.M + f2i r
          let x := if M > 0 then tdiv (M - 1) 12 else tdiv (M - 12) 12
          (computeFloor { p with M := M - x * 12, Y := p.Y + x, validJD := false }, r - Float.ofInt (f2i r))
        else if i == 5 then
          let p := computeYMD_HMS p
          (computeFloor { p with Y := p.Y + f2i r, validJD := false }, r - Float.ofInt (f2i r))
        else (p, r)
      let p := computeJD p
      some (clearYMD_HMS_TZ { p with iJD := p.iJD + Float.toInt64 (r * 1000.0 * xf + rRounder) })
  if byteAt z n == 45 then
    if z0 != 43 && z0 != 45 then none else
    let k := n - 1
    let sh := n - 5
    match gd z 1 k 0 14712 45, gd z (k + 2) 2 0 12 45, gd z (k + 5) 2 0 31 0 with
    | some Y, some M, some D =>
      if M ≥ 12 || D ≥ 31 then none else
      let p := computeYMD_HMS p
      let p := { p with validJD := false }
      let (p, D) : DT × Int :=
        if z0 == 45 then ({ p with Y := p.Y - Y, M := p.M - M }, -(D : Int))
        else ({ p with Y := p.Y + Y, M := p.M + M }, (D : Int))
      let x := if p.M > 0 then tdiv (p.M - 1) 12 else tdiv (p.M - 12) 12
      let p := computeFloor { p with Y := p.Y + x, M := p.M - x * 12 }
      let p := computeJD p
      let p := { p with validHMS := false, validYMD := false }
      let p := { p with iJD := p.iJD + i64 D * msDay }
      if byteAt z (11 + sh) == 0 then some p
      else if isSpace (byteAt z (11 + sh)) && (gd z (12 + sh) 2 0 24 58).isSome && (gd z (15 + sh) 2 0 59 0).isSome then
        timeShift z (12 + sh) z0 p
      else none
    | _, _, _ => none
  else if byteAt z n == 58 then timeShift z 0 z0 p
  else unitForm p

/-- date.c autoAdjustDate. -/
def autoAdjust (p : DT) : DT :=
  if !p.rawS || p.validJD then { p with rawS := false }
  else if p.s ≥ -210866760000.0 && p.s ≤ 253402300799.0 then
    let r := p.s * 1000.0 + 210866760000000.0
    { clearYMD_HMS_TZ p with iJD := Float.toInt64 (r + 0.5), validJD := true, rawS := false }
  else p

/-- date.c parseModifier. none: an unknown or malformed modifier. idx is the 1-based modifier number. -/
def parseModifier (z : ByteArray) (p : DT) (idx : Nat) : Option DT :=
  match lowerB (byteAt z 0) with
  | 97 => if ieq z "auto" then (if idx > 1 then none else some (autoAdjust p)) else none
  | 99 =>
    if ieq z "ceiling" then some { clearYMD_HMS_TZ (computeJD p) with nFloor := 0 } else none
  | 101 =>
    if !startsI z "end of " then none
    else if !p.validJD && !p.validYMD && !p.validHMS then none
    else
      let z := z.extract 7 z.size
      let p := computeYMD p
      let p := { p with validHMS := true, h := 23, m := 59, s := 59.999, rawS := false, tz := 0, validJD := false }
      if ieq z "month" then
        let p := { p with D := 1, M := p.M + 1 }
        let p := if p.M > 12 then { p with Y := p.Y + 1, M := 1 } else p
        let p := computeJD (computeFloor p)
        some (clearYMD_HMS_TZ { p with iJD := p.iJD - i64 (p.nFloor + 1) * msDay })
      else if ieq z "year" then some { p with M := 12, D := 31, nFloor := 0 }
      else if ieq z "day" then some p
      else none
  | 102 =>
    if ieq z "floor" then
      let p := computeJD p
      some (clearYMD_HMS_TZ { p with iJD := p.iJD - i64 p.nFloor * msDay, nFloor := 0 })
    else none
  | 106 =>
    if ieq z "julianday" then
      if idx > 1 then none else if p.validJD && p.rawS then some { p with rawS := false } else none
    else none
  | 108 =>
    if ieq z "localtime" then
      some { (if p.isLocal then p else toLocaltime p) with isUtc := false, isLocal := true }
    else none
  | 117 =>
    if ieq z "unixepoch" && p.rawS then
      if idx > 1 then none else
      let r := p.s * 1000.0 + 210866760000000.0
      if r ≥ 0.0 && r < 464269060800000.0 then
        some { clearYMD_HMS_TZ p with iJD := Float.toInt64 (r + 0.5), validJD := true, rawS := false }
      else none
    else if ieq z "utc" then
      if p.isUtc then some p else
      let p := computeJD p
      let guess := utcLoop p.iJD p.iJD 0 4
      some { iJD := guess, validJD := true, isUtc := true, useSubsec := p.useSubsec }
    else none
  | 119 =>
    if startsI z "weekday " then
      let ar := atoFBytes (z.extract 8 z.size)
      let r := ar.value
      let n := f2i r
      if ar.rc > 0 && r ≥ -6.0 && r ≤ 6.0 && realSameAsInt r (i64 n) then
        let p := computeYMD_HMS p
        let p := computeJD { p with tz := 0, validJD := false }
        let Z : Int64 := ((p.iJD + 129600000) / msDay) % 7
        let n : Int64 := i64 n.natAbs
        let iJD :=
          if Z != n then
            let Z := if Z > n then Z - 7 else Z
            let iJD := p.iJD + (n - Z) * msDay
            if hasByte z 45 8 (z.size + 1) then iJD - 7 * msDay else iJD
          else p.iJD
        some { clearYMD_HMS_TZ p with iJD := iJD, nFloor := 0 }
      else none
    else none
  | 115 =>
    if !startsI z "start of " then
      if ieq z "subsec" || ieq z "subsecond" then some { p with useSubsec := true } else none
    else if !p.validJD && !p.validYMD && !p.validHMS then none
    else
      let z := z.extract 9 z.size
      let p := computeYMD p
      let p := { p with validHMS := true, h := 0, m := 0, s := 0.0, rawS := false, tz := 0, validJD := false }
      if ieq z "month" then some { p with D := 1, nFloor := 0 }
      else if ieq z "year" then some { p with M := 1, D := 1, nFloor := 0 }
      else if ieq z "day" then some p
      else none
  | c => if c == 43 || c == 45 || (48 ≤ c && c ≤ 57) then numericMod z p else none

/-! ### isDate -/

/-- sqlite3_value_text as the bytes of a C string. -/
def valueText : Value → Option ByteArray
  | .null => none
  | .int i => some (int64ToBytes i)
  | .real f => some (fmtRealBytes f)
  | .text s => some (cstr s.toUTF8)
  | .blob b => some (cstr b)

private def modLoop (args : Array Value) (now : Option Int64) (p : DT) (i : Nat) : Nat → Option DT
  | 0 => some p
  | f + 1 =>
    if h : i < args.size then
      match valueText args[i] with
      | none => none
      | some z =>
        match parseModifier z p i with
        | none => none
        | some p => modLoop args now p (i + 1) f
    else some p

/-- date.c isDate: the time value args[0] (now when there are no arguments) with the modifiers args[1...]. -/
def isDate (args : Array Value) (now : Option Int64) : Option DT :=
  let start : Option DT :=
    match args[0]? with
    | none => setCurrent now {}
    | some (Value.int i) => some (setRaw {} (Float.ofInt i.toInt))
    | some (Value.real f) => some (setRaw {} f)
    | some Value.null => none
    | some v => (valueText v).bind fun z => parseDateOrTime z now {}
  match start with
  | none => none
  | some p =>
    match modLoop args now p 1 (args.size + 1) with
    | none => none
    | some p =>
      let p := computeJD p
      if p.isError || !validJulianDay p.iJD then none
      else some (if p.validYMD && p.D > 28 then { p with validYMD := false } else p)

/-! ### Output -/

@[inline] private def dig (n : Int) : UInt8 := (n.toNat % 10 + 48).toUInt8

/-- C's "%0wd" (zero true) or "%wd" of v. -/
def appendPad (out : ByteArray) (v : Int) (w : Nat) (zero : Bool) : ByteArray :=
  if 0 ≤ v && v < 100 && w == 2 then
    let a := v.toNat / 10
    let out := if a == 0 && !zero then out.push 32 else out.push (a + 48).toUInt8
    out.push (v.toNat % 10 + 48).toUInt8
  else
    let ds := (toString v.natAbs).toUTF8
    let neg := v < 0
    let len := ds.size + (if neg then 1 else 0)
    let padN := w - len
    if zero then (((if neg then out.push 45 else out) ++ bytesRepeat 48 padN) ++ ds)
    else ((out ++ bytesRepeat 32 padN) ++ (if neg then ByteArray.empty.push 45 else ByteArray.empty)) ++ ds

private def fmtF (fmt : String) (f : Float) : ByteArray :=
  (printfBytes? fmt.toUTF8 #[.real f]).getD ByteArray.empty

private def appendYMD (out : ByteArray) (x : DT) : ByteArray :=
  let Y := x.Y.natAbs
  let out := if x.Y < 0 then out.push 45 else out
  let out := out.push (dig (Y / 1000 : Nat)) |>.push (dig (Y / 100 : Nat)) |>.push (dig (Y / 10 : Nat)) |>.push (dig Y)
  let out := out.push 45 |>.push (dig (x.M / 10)) |>.push (dig x.M) |>.push 45
  out.push (dig (x.D / 10)) |>.push (dig x.D)

private def appendHMS (out : ByteArray) (x : DT) : ByteArray :=
  let out := out.push (dig (x.h / 10)) |>.push (dig x.h) |>.push 58 |>.push (dig (x.m / 10)) |>.push (dig x.m) |>.push 58
  if x.useSubsec then
    let s := f2i (1000.0 * x.s + 0.5)
    out.push (dig (s / 10000)) |>.push (dig (s / 1000)) |>.push 46 |>.push (dig (s / 100)) |>.push (dig (s / 10)) |>.push (dig s)
  else
    let s := f2i x.s
    out.push (dig (s / 10)) |>.push (dig s)

private def textOf (b : ByteArray) : Value := .text (bytesToString b)

/-- date(): YYYY-MM-DD. -/
def dateFn (x : DT) : Value :=
  textOf (appendYMD ByteArray.empty (computeYMD x))

/-- time(): HH:MM:SS (HH:MM:SS.SSS after the subsec modifier). -/
def timeFn (x : DT) : Value :=
  textOf (appendHMS ByteArray.empty (computeHMS x))

/-- datetime(): YYYY-MM-DD HH:MM:SS. -/
def datetimeFn (x : DT) : Value :=
  let x := computeYMD_HMS x
  textOf (appendHMS (appendYMD ByteArray.empty x |>.push 32) x)

def juliandayFn (x : DT) : Value := .real (Float.ofInt (computeJD x).iJD.toInt / 86400000.0)

def unixepochFn (x : DT) : Value :=
  let x := computeJD x
  if x.useSubsec then .real (Float.ofInt (x.iJD - unixOffsetMs).toInt / 1000.0)
  else .int (x.iJD / 1000 - 210866760000)

private def daysAfterJan01 (p : DT) : Int :=
  let jan := computeJD { p with validJD := false, M := 1, D := 1 }
  ((p.iJD - jan.iJD + 43200000) / msDay).toInt

private def daysAfterMonday (p : DT) : Int := Int.tmod ((p.iJD + 43200000) / msDay).toInt 7
private def daysAfterSunday (p : DT) : Int := Int.tmod ((p.iJD + 129600000) / msDay).toInt 7

/-- x moved to the Thursday of its ISO week, with its date recomputed. -/
private def thursday (x : DT) : DT :=
  computeYMD { x with iJD := x.iJD + i64 (3 - daysAfterMonday x) * msDay, validYMD := false }

/-- One strftime conversion; none for an unknown one. -/
private def fmtOne (cf : UInt8) (x : DT) (out : ByteArray) : Option ByteArray :=
  match cf with
  | 100 => some (appendPad out x.D 2 true)
  | 101 => some (appendPad out x.D 2 false)
  | 102 => some (out ++ fmtF "%06.3f" (if x.s > 59.999 then 59.999 else x.s))
  | 70 => some (appendPad ((appendPad (appendPad out x.Y 4 true |>.push 45) x.M 2 true).push 45) x.D 2 true)
  | 71 => some (appendPad out (thursday x).Y 4 true)
  | 103 => some (appendPad out (Int.tmod (thursday x).Y 100) 2 true)
  | 72 => some (appendPad out x.h 2 true)
  | 107 => some (appendPad out x.h 2 false)
  | 73 | 108 =>
    let h := if x.h > 12 then x.h - 12 else x.h
    some (appendPad out (if h == 0 then 12 else h) 2 (cf == 73))
  | 106 => some (appendPad out (daysAfterJan01 x + 1) 3 true)
  | 74 => some (out ++ fmtF "%.16g" (Float.ofInt x.iJD.toInt / 86400000.0))
  | 109 => some (appendPad out x.M 2 true)
  | 77 => some (appendPad out x.m 2 true)
  | 112 => some (out ++ (if x.h ≥ 12 then "PM" else "AM").toUTF8)
  | 80 => some (out ++ (if x.h ≥ 12 then "pm" else "am").toUTF8)
  | 82 => some (appendPad (appendPad out x.h 2 true |>.push 58) x.m 2 true)
  | 115 =>
    if x.useSubsec then some (out ++ fmtF "%.3f" (Float.ofInt (x.iJD - unixOffsetMs).toInt / 1000.0))
    else some (out ++ int64ToBytes (x.iJD / 1000 - 210866760000))
  | 83 => some (appendPad out (f2i x.s) 2 true)
  | 84 => some (appendPad ((appendPad (appendPad out x.h 2 true |>.push 58) x.m 2 true).push 58) (f2i x.s) 2 true)
  | 117 | 119 =>
    let d := daysAfterSunday x
    some (out.push (if d == 0 && cf == 117 then 55 else (d.toNat + 48).toUInt8))
  | 85 => some (appendPad out (tdiv (daysAfterJan01 x - daysAfterSunday x + 7) 7) 2 true)
  | 86 => some (appendPad out (tdiv (daysAfterJan01 (thursday x)) 7 + 1) 2 true)
  | 87 => some (appendPad out (tdiv (daysAfterJan01 x - daysAfterMonday x + 7) 7) 2 true)
  | 89 => some (appendPad out x.Y 4 true)
  | 37 => some (out.push 37)
  | _ => none

private def fmtLoop (fmt : ByteArray) (x : DT) (i : Nat) (out : ByteArray) : Nat → Option ByteArray
  | 0 => some out
  | f + 1 =>
    if h : i < fmt.size then
      let c := fmt[i]
      if c != 37 then fmtLoop fmt x (i + 1) (out.push c) f
      else
        match fmtOne (byteAt fmt (i + 1)) x out with
        | none => none
        | some out => fmtLoop fmt x (i + 2) out f
    else some out

/-- strftime(fmt, time-value, modifiers...): an unknown conversion gives NULL. -/
def strftimeFn (args : Array Value) (now : Option Int64) : Value :=
  match args[0]? with
  | none => .null
  | some fv =>
    match valueText fv with
    | none => .null
    | some fmt =>
      match isDate (args.extract 1 args.size) now with
      | none => .null
      | some x =>
        let x := computeYMD_HMS (computeJD x)
        match fmtLoop fmt x 0 ByteArray.empty (fmt.size + 1) with
        | none => .null
        | some out => textOf out

private def timediffLoop (up : Bool) (d1 : DT) (d2 : DT) (Y M : Int) : Nat → DT × Int × Int
  | 0 => (d2, Y, M)
  | f + 1 =>
    if (if up then d1.iJD < d2.iJD else d1.iJD > d2.iJD) then
      let (Y, M) := if M - 1 < 0 then (Y - 1, (11 : Int)) else (Y, M - 1)
      let d2 :=
        if up then (if d2.M - 1 < 1 then { d2 with M := 12, Y := d2.Y - 1 } else { d2 with M := d2.M - 1 })
        else (if d2.M + 1 > 12 then { d2 with M := 1, Y := d2.Y + 1 } else { d2 with M := d2.M + 1 })
      timediffLoop up d1 (computeJD { d2 with validJD := false }) Y M f
    else (d2, Y, M)

/-- date.c timediffFunc. -/
def timediffFn (a b : Value) (now : Option Int64) : Value :=
  match isDate #[a] now, isDate #[b] now with
  | some d1, some d2 =>
    let d1 := computeYMD_HMS d1
    let d2 := computeYMD_HMS d2
    let up := d1.iJD ≥ d2.iJD
    let Y := if up then d1.Y - d2.Y else d2.Y - d1.Y
    let d2 := if Y != 0 then computeJD { d2 with Y := d1.Y, validJD := false } else d2
    let M := if up then d1.M - d2.M else d2.M - d1.M
    let (Y, M) := if M < 0 then (Y - 1, M + 12) else (Y, M)
    let d2 := if M != 0 then computeJD { d2 with M := d1.M, validJD := false } else d2
    let (d2, Y, M) := timediffLoop up d1 d2 Y M 1000
    let iJD := (if up then d1.iJD - d2.iJD else d2.iJD - d1.iJD) + 148699540800000
    let d1 := computeYMD_HMS (clearYMD_HMS_TZ { d1 with iJD := iJD })
    let out := (ByteArray.empty.push (if up then 43 else 45))
    let out := appendPad out Y 4 true |>.push 45
    let out := appendPad out M 2 true |>.push 45
    let out := appendPad out (d1.D - 1) 2 true |>.push 32
    let out := appendPad out d1.h 2 true |>.push 58
    let out := appendPad out d1.m 2 true |>.push 58
    textOf (out ++ fmtF "%06.3f" d1.s)
  | _, _ => .null

/-- Whether name (upper case) is one of the functions of this module. -/
def isDateFn (name : String) : Bool :=
  match name with
  | "DATE" | "TIME" | "DATETIME" | "JULIANDAY" | "UNIXEPOCH" | "STRFTIME" | "TIMEDIFF"
  | "CURRENT_DATE" | "CURRENT_TIME" | "CURRENT_TIMESTAMP" => true
  | _ => false

/-- The SQL function `name` (upper case: DATE, TIME, DATETIME, JULIANDAY, UNIXEPOCH, STRFTIME, TIMEDIFF,
and the argument-less CURRENT_DATE, CURRENT_TIME, CURRENT_TIMESTAMP) applied to its arguments, as sqlite3 3.54 computes it.
nowMs: the statement's current time as Unix milliseconds (sqlite reads the clock once per statement); none: 'now'
gives NULL. A malformed time value or modifier gives NULL, as sqlite does. The local time zone is taken to be UTC:
'localtime' and 'utc' are identity conversions on the calendar fields. -/
def call (name : String) (args : Array Value) (nowMs : Option Int64) : Except String Value :=
  let with1 (f : DT → Value) : Except String Value :=
    .ok (match isDate args nowMs with | some x => f x | none => .null)
  match name with
  | "DATE" => with1 dateFn
  | "TIME" => with1 timeFn
  | "DATETIME" => with1 datetimeFn
  | "JULIANDAY" => with1 juliandayFn
  | "UNIXEPOCH" => with1 unixepochFn
  | "STRFTIME" => .ok (strftimeFn args nowMs)
  | "TIMEDIFF" =>
    match args[0]?, args[1]? with
    | some a, some b => if args.size == 2 then .ok (timediffFn a b nowMs) else .error "wrong number of arguments to function timediff()"
    | _, _ => .error "wrong number of arguments to function timediff()"
  | "CURRENT_DATE" => if args.isEmpty then with1 dateFn else .error "wrong number of arguments to function current_date()"
  | "CURRENT_TIME" => if args.isEmpty then with1 timeFn else .error "wrong number of arguments to function current_time()"
  | "CURRENT_TIMESTAMP" => if args.isEmpty then with1 datetimeFn else .error "wrong number of arguments to function current_timestamp()"
  | _ => .error s!"no such function: {name}"

end LSql.DateTime

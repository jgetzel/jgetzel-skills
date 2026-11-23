import LSql.Num
import LSql.Value
import LSql.Func
/-! sqlite's JSON functions (json.c, text JSON): parsing (with the JSON5 numbers, trailing commas and
Infinity/NaN that sqlite accepts), minified and pretty output, paths ($.a, ."a b", [N], [#-N]) with lookup and
edit, json_each/json_tree, the scalar functions and the two aggregates. A document is parsed into a tree (J) that
remembers the size its JSONB encoding would have, because json_each/json_tree report JSONB offsets as "id". -/
namespace LSql.Json
open LSql

/-- JSON_MAX_DEPTH. -/
def maxDepth : Nat := 1000

/-! ### Bytes -/

@[inline] def bAt (z : ByteArray) (i : Nat) : UInt8 := if h : i < z.size then z[i] else 0
@[inline] def isDig (c : UInt8) : Bool := c >= 48 && c <= 57
@[inline] def isHex (c : UInt8) : Bool := isDig c || (c >= 97 && c <= 102) || (c >= 65 && c <= 70)
@[inline] def isAlpha (c : UInt8) : Bool := (c >= 97 && c <= 122) || (c >= 65 && c <= 90)
@[inline] def isAlnum (c : UInt8) : Bool := isDig c || isAlpha c
@[inline] def isSp (c : UInt8) : Bool := c == 32 || c == 9 || c == 10 || c == 13

def hexVal (c : UInt8) : Nat :=
  if isDig c then (c - 48).toNat else if c >= 97 then (c - 87).toNat else (c - 55).toNat

/-- Append src[a, b) to out. -/
@[inline] def appendRange (out src : ByteArray) (a b : Nat) : ByteArray :=
  if b > a then src.copySlice a out out.size (b - a) false else out

def bs (s : String) : ByteArray := s.toUTF8

def bytesEq (a b : ByteArray) : Bool := a.size == b.size && a.data == b.data

def skipWs (z : ByteArray) (i : Nat) : Nat :=
  if h : i < z.size then
    if isSp z[i] then skipWs z (i + 1) else i
  else i
termination_by z.size - i

/-- Case-insensitive match of an ASCII lower-case literal at i. -/
def ciMatch (z : ByteArray) (i : Nat) (lit : ByteArray) : Bool := Id.run do
  for k in [0:lit.size] do
    let c := bAt z (i + k)
    let c := if c >= 65 && c <= 90 then c + 32 else c
    if c != bAt lit k then return false
  return true

def litAt (z : ByteArray) (i : Nat) (lit : ByteArray) : Bool := Id.run do
  for k in [0:lit.size] do
    if bAt z (i + k) != bAt lit k then return false
  return true

/-- Index of the first byte equal to c at or after i, or the size. -/
def findByte (z : ByteArray) (c : UInt8) (i : Nat) : Nat :=
  if h : i < z.size then
    if z[i] == c then i else findByte z c (i + 1)
  else z.size
termination_by z.size - i

/-! ### The tree -/

/-- A JSON string as it appears between its quotes. esc: has a backslash escape; t5: needs translating on output (a literal control character, a JSON5 escape, a raw double quote). -/
structure Str where
  raw : ByteArray
  esc : Bool := false
  t5 : Bool := false

inductive J where
  | null | tru | fls
  | int (raw : ByteArray)
  | flt (raw : ByteArray)
  | str (s : Str)
  /-- A JSON5 number literal (hex integer, bare point, ...): orig as written, canon as sqlite renders it. -/
  | lit (orig : ByteArray) (canon : J)
  /-- sz: the payload size of the array's JSONB encoding. -/
  | arr (xs : Array J) (sz : Nat)
  | obj (kvs : Array (Str × J)) (sz : Nat)

instance : Inhabited J := ⟨.null⟩

/-- Header bytes of a JSONB element with an n byte payload. -/
def hdrSize (n : Nat) : Nat :=
  if n <= 11 then 1 else if n <= 0xff then 2 else if n <= 0xffff then 3 else if n <= 0xffffffff then 5 else 9

def Str.size (s : Str) : Nat := hdrSize s.raw.size + s.raw.size

/-- The node without its JSON5 spelling. -/
def J.canon : J → J
  | .lit _ c => c
  | j => j

/-- Size of the JSONB encoding. -/
def J.size : J → Nat
  | .lit o _ => hdrSize o.size + o.size
  | .null | .tru | .fls => 1
  | .int r | .flt r => hdrSize r.size + r.size
  | .str s => s.size
  | .arr _ n | .obj _ n => hdrSize n + n

/-- Header size of the JSONB encoding. -/
def J.hdr : J → Nat
  | .lit o _ => hdrSize o.size
  | .null | .tru | .fls => 1
  | .int r | .flt r => hdrSize r.size
  | .str s => hdrSize s.raw.size
  | .arr _ n | .obj _ n => hdrSize n

def mkArr (xs : Array J) : J := .arr xs (xs.foldl (fun a x => a + x.size) 0)
def mkObj (kvs : Array (Str × J)) : J := .obj kvs (kvs.foldl (fun a kv => a + kv.1.size + kv.2.size) 0)

def J.isContainer : J → Bool
  | .arr .. | .obj .. => true
  | _ => false

def J.typeName (j : J) : String :=
  match j.canon with
  | .null => "null" | .tru => "true" | .fls => "false" | .int _ => "integer" | .flt _ => "real"
  | .str _ => "text" | .arr .. => "array" | .obj .. => "object" | .lit .. => "integer"

/-! ### Unescaping -/

def hex4 (z : ByteArray) (i : Nat) : Nat :=
  hexVal (bAt z i) * 4096 + hexVal (bAt z (i + 1)) * 256 + hexVal (bAt z (i + 2)) * 16 + hexVal (bAt z (i + 3))

def isHex4 (z : ByteArray) (i : Nat) : Bool :=
  isHex (bAt z i) && isHex (bAt z (i + 1)) && isHex (bAt z (i + 2)) && isHex (bAt z (i + 3))

/-- Append the UTF-8 encoding of a code point (surrogates as three bytes, as sqlite does). -/
def pushUtf8 (o : ByteArray) (v : Nat) : ByteArray :=
  if v <= 0x7f then o.push v.toUInt8
  else if v <= 0x7ff then (o.push (0xc0 + v / 64).toUInt8).push (0x80 + v % 64).toUInt8
  else if v < 0x10000 then
    ((o.push (0xe0 + v / 4096).toUInt8).push (0x80 + (v / 64) % 64).toUInt8).push (0x80 + v % 64).toUInt8
  else
    (((o.push (0xf0 + v / 262144).toUInt8).push (0x80 + (v / 4096) % 64).toUInt8).push
      (0x80 + (v / 64) % 64).toUInt8).push (0x80 + v % 64).toUInt8

def unescapeGo (raw : ByteArray) (fuel i : Nat) (o : ByteArray) : ByteArray :=
  match fuel with
  | 0 => o
  | fuel + 1 =>
    if i >= raw.size then o else
    let e := findByte raw 92 i
    let o := appendRange o raw i e
    if e >= raw.size then o else
    let c := bAt raw (e + 1)
    let rem := raw.size - e
    if c == 117 then
      if rem < 6 then o else
      let v := hex4 raw (e + 2)
      if (v &&& 0xfc00) == 0xd800 && rem >= 12 && bAt raw (e + 6) == 92 && bAt raw (e + 7) == 117
          && (hex4 raw (e + 8) &&& 0xfc00) == 0xdc00 then
        let vlo := hex4 raw (e + 8)
        unescapeGo raw fuel (e + 12) (pushUtf8 o (((v &&& 0x3ff) <<< 10) + (vlo &&& 0x3ff) + 0x10000))
      else unescapeGo raw fuel (e + 6) (pushUtf8 o v)
    else if c == 120 then
      if rem < 4 then o else unescapeGo raw fuel (e + 4) (o.push (hexVal (bAt raw (e + 2)) * 16 + hexVal (bAt raw (e + 3))).toUInt8)
    else if c == 10 then unescapeGo raw fuel (e + 2) o
    else if c == 13 then unescapeGo raw fuel (e + (if bAt raw (e + 2) == 10 then 3 else 2)) o
    else if c == 0xe2 then unescapeGo raw fuel (e + 4) o
    else
      let o :=
        if c == 98 then o.push 8 else if c == 102 then o.push 12 else if c == 110 then o.push 10
        else if c == 114 then o.push 13 else if c == 116 then o.push 9 else if c == 118 then o.push 11
        else if c == 48 then o.push 0
        else if c == 34 || c == 47 || c == 92 || c == 39 then o.push c
        else o
      unescapeGo raw fuel (e + 2) o

/-- The text a JSON string (its raw bytes between the quotes) stands for. -/
def unescape (raw : ByteArray) : ByteArray := unescapeGo raw (raw.size + 1) 0 ByteArray.empty

def Str.bytes (s : Str) : ByteArray := if s.esc then unescape s.raw else s.raw

/-- Two labels are equal (jsonLabelCompare): escapes decoded when either has one. -/
def labelEq (a b : Str) : Bool :=
  if !a.esc && !b.esc then bytesEq a.raw b.raw else bytesEq (unescape a.raw) (unescape b.raw)

/-! ### Output -/

def hexd (n : UInt8) : UInt8 := if n < 10 then 48 + n else 87 + n

/-- A control character as jsonAppendControlChar writes it. -/
def ctlEsc (o : ByteArray) (c : UInt8) : ByteArray :=
  if c == 8 then (o.push 92).push 98
  else if c == 9 then (o.push 92).push 116
  else if c == 10 then (o.push 92).push 110
  else if c == 12 then (o.push 92).push 102
  else if c == 13 then (o.push 92).push 114
  else (((((o.push 92).push 117).push 48).push 48).push (hexd (c >>> 4))).push (hexd (c &&& 15))

def escGo (o s : ByteArray) (fuel i start : Nat) : ByteArray :=
  match fuel with
  | 0 => appendRange o s start s.size
  | fuel + 1 =>
    if h : i < s.size then
      let c := s[i]
      if c >= 32 && c != 34 && c != 92 then escGo o s fuel (i + 1) start
      else
        let o := appendRange o s start i
        let o := if c == 34 || c == 92 then (o.push 92).push c else ctlEsc o c
        escGo o s fuel (i + 1) (i + 1)
    else appendRange o s start i

/-- Append s with " and \ and control characters escaped (no quotes). -/
def appendEscaped (o s : ByteArray) : ByteArray := escGo o s (s.size + 1) 0 0

/-- jsonAppendString: s in double quotes, escaped. -/
def appendQuoted (o s : ByteArray) : ByteArray := (appendEscaped (o.push 34) s).push 34

/-- A SQL text as a JSON string. -/
def quoteStr (s : ByteArray) : Str :=
  let e := appendEscaped ByteArray.empty s
  { raw := e, esc := e.size != s.size, t5 := false }

/-- The \u00XX escape of a byte given as two hex digits. -/
def u00 (o : ByteArray) (h l : UInt8) : ByteArray := ((((o.push 92).push 117).push 48).push 48).push h |>.push l

/-- A TEXT5 string (jsonTranslateBlobToText, JSONB_TEXT5) as canonical JSON string contents. -/
def t5Translate (raw : ByteArray) : ByteArray := Id.run do
  let mut o := ByteArray.empty
  let mut i := 0
  for _ in [0:raw.size + 1] do
    if i >= raw.size then break
    let c := bAt raw i
    if c == 34 then
      o := (o.push 92).push 34
      i := i + 1
    else if c < 32 then
      o := ctlEsc o c
      i := i + 1
    else if c == 92 then
      let c2 := bAt raw (i + 1)
      if c2 == 39 then
        o := o.push 39
        i := i + 2
      else if c2 == 118 then
        o := u00 o 48 98
        i := i + 2
      else if c2 == 120 then
        o := u00 o (bAt raw (i + 2)) (bAt raw (i + 3))
        i := i + 4
      else if c2 == 48 then
        o := u00 o 48 48
        i := i + 2
      else if c2 == 13 then i := i + (if bAt raw (i + 2) == 10 then 3 else 2)
      else if c2 == 10 then i := i + 2
      else if c2 == 0xe2 then i := i + 4
      else
        o := (o.push 92).push c2
        i := i + 2
    else
      o := o.push c
      i := i + 1
  return o

def appendStr (o : ByteArray) (s : Str) : ByteArray :=
  if s.t5 then (ByteArray.append (o.push 34) (t5Translate s.raw)).push 34
  else (appendRange (o.push 34) s.raw 0 s.raw.size).push 34

def renderJ (fuel : Nat) (j : J) (o : ByteArray) : ByteArray :=
  match fuel with
  | 0 => o
  | fuel + 1 =>
    match j with
    | .null => ByteArray.append o (bs "null")
    | .tru => ByteArray.append o (bs "true")
    | .fls => ByteArray.append o (bs "false")
    | .int r | .flt r => ByteArray.append o r
    | .lit _ c => renderJ fuel c o
    | .str s => appendStr o s
    | .arr xs _ => Id.run do
      let mut o := o.push 91
      let mut first := true
      for x in xs do
        if !first then o := o.push 44
        first := false
        o := renderJ fuel x o
      return o.push 93
    | .obj kvs _ => Id.run do
      let mut o := o.push 123
      let mut first := true
      for kv in kvs do
        if !first then o := o.push 44
        first := false
        o := renderJ fuel kv.2 ((appendStr o kv.1).push 58)
      return o.push 125

def render (j : J) : ByteArray := renderJ (maxDepth + 100) j ByteArray.empty

def indentN (o ind : ByteArray) (n : Nat) : ByteArray := Id.run do
  let mut o := o
  for _ in [0:n] do
    o := ByteArray.append o ind
  return o

/-- json_pretty. -/
def prettyJ (fuel : Nat) (ind : ByteArray) (lvl : Nat) (j : J) (o : ByteArray) : ByteArray :=
  match fuel with
  | 0 => o
  | fuel + 1 =>
    match j with
    | .arr xs _ =>
      if xs.isEmpty then (o.push 91).push 93 else Id.run do
        let mut o := (o.push 91).push 10
        let mut k := 0
        for x in xs do
          o := indentN o ind (lvl + 1)
          o := prettyJ fuel ind (lvl + 1) x o
          k := k + 1
          if k < xs.size then o := (o.push 44).push 10
        o := (o.push 10)
        o := indentN o ind lvl
        return o.push 93
    | .obj kvs _ =>
      if kvs.isEmpty then (o.push 123).push 125 else Id.run do
        let mut o := (o.push 123).push 10
        let mut k := 0
        for kv in kvs do
          o := indentN o ind (lvl + 1)
          o := appendStr o kv.1
          o := (o.push 58).push 32
          o := prettyJ fuel ind (lvl + 1) kv.2 o
          k := k + 1
          if k < kvs.size then o := (o.push 44).push 10
        o := (o.push 10)
        o := indentN o ind lvl
        return o.push 125
    | _ => renderJ fuel j o

/-! ### Parsing (jsonTranslateTextToBlob) -/

inductive PR where
  /-- ie: sqlite's iErr as the parse left it (the last structural token read as a value), if it was set. -/
  | val (next : Nat) (j : J) (ns : Bool) (ie : Option Nat)
  /-- A structural token where a value was expected: 0 end of text, 2 '}', 3 ']', 4 ',', 5 ':'; pos is sqlite's iErr. -/
  | tok (code pos : Nat)
  | fail (pos : Nat)

inductive CI where
  | i (v : Int64)
  | r (f : Float)
  | bad

/-- jsonConvertInteger on a decimal or 0x hexadecimal literal. -/
def convertInteger (z : ByteArray) : CI := Id.run do
  let sz := z.size
  if sz == 0 then return .bad
  let neg := bAt z 0 == 45
  let k0 := if neg || bAt z 0 == 43 then 1 else 0
  let mut u : UInt64 := 0
  let mut ro : Float := 1.0
  if k0 + 2 < sz && bAt z k0 == 48 && (bAt z (k0 + 1) == 120 || bAt z (k0 + 1) == 88) then
    for k in [k0 + 2:sz] do
      let c := bAt z k
      if !isHex c then return .bad
      if (u >>> 60) != 0 then ro := ro * 16.0 else u := u * 16 + (hexVal c).toUInt64
  else if k0 >= sz then return .bad
  else
    for k in [k0:sz] do
      let c := bAt z k
      if !isDig c then return .bad
      if (u >>> 60) != 0 then ro := ro * 10.0 else u := u * 10 + (c - 48).toUInt64
  if ro > 1.0 || (u > 0x7fffffffffffffff && (!neg || u > 0x8000000000000000)) then
    let r := ro * u.toFloat
    return .r (if neg then -r else r)
  else
    let v := u.toInt64
    return .i (if neg && u != 0x8000000000000000 then 0 - v else v)

/-- The value of a 0x literal, sign ignored. -/
def hexLitVal (raw : ByteArray) : Nat := Id.run do
  let k0 := if bAt raw 0 == 45 || bAt raw 0 == 43 then 1 else 0
  let mut u : Nat := 0
  for k in [k0 + 2:raw.size] do
    u := u * 16 + hexVal (bAt raw k)
  return u

/-- An INT5 literal (hexadecimal) as sqlite 3.54 writes it: unsigned decimal, or 9.0e999 beyond 64 bits. -/
def hexInt5 (raw : ByteArray) : J := Id.run do
  let neg := bAt raw 0 == 45
  let k0 := if neg || bAt raw 0 == 43 then 1 else 0
  let mut u : Nat := 0
  for k in [k0 + 2:raw.size] do
    u := u * 16 + hexVal (bAt raw k)
  if u >= 18446744073709551616 then return .flt (bs (if neg then "-9.0e999" else "9.0e999"))
  let t := (toString u).toUTF8
  return .int (if neg then (ByteArray.empty.push 45) ++ t else t)

/-- A FLOAT5 literal as text: digits added beside a bare point. -/
def float5Text (raw : ByteArray) : ByteArray := Id.run do
  let mut o := ByteArray.empty
  let mut k := 0
  if bAt raw 0 == 45 then
    o := o.push 45
    k := 1
  if bAt raw k == 46 then o := o.push 48
  for m in [k:raw.size] do
    let c := bAt raw m
    o := o.push c
    if c == 46 && (m + 1 == raw.size || !isDig (bAt raw (m + 1))) then o := o.push 48
  return o

def numLoop (z : ByteArray) (i : Nat) (fuel j t : Nat) (seenE ns : Bool) : Except Nat (Nat × Nat × Bool) :=
  match fuel with
  | 0 => .error j
  | fuel + 1 =>
    let c := bAt z j
    if isDig c then numLoop z i fuel (j + 1) t seenE ns
    else if c == 46 then
      if (t &&& 2) != 0 then .error j else numLoop z i fuel (j + 1) (t ||| 2) seenE ns
    else if c == 101 || c == 69 then
      let prev := bAt z (j - 1)
      let r : Option (Nat × Bool) :=
        if prev < 48 then
          if prev == 46 && j >= i + 2 && isDig (bAt z (j - 2)) then some (t ||| 1, true) else none
        else some (t, ns)
      match r with
      | none => .error j
      | some (t, ns) =>
        if seenE then .error j else
        let t := t ||| 2
        let c1 := bAt z (j + 1)
        let j' := if c1 == 43 || c1 == 45 then j + 1 else j
        let c2 := bAt z (j' + 1)
        if c2 < 48 || c2 > 57 then .error j' else numLoop z i fuel (j' + 1) t true ns
    else
      let prev := bAt z (j - 1)
      if prev < 48 then
        if prev == 46 && j >= i + 2 && isDig (bAt z (j - 2)) then .ok (j, t ||| 1, true) else .error j
      else .ok (j, t, ns)

def hexEnd (z : ByteArray) (fuel j : Nat) : Nat :=
  match fuel with
  | 0 => j
  | fuel + 1 => if isHex (bAt z j) then hexEnd z fuel (j + 1) else j

/-- The number starting at i: (end, node, nonstandard) or sqlite's error position. -/
def parseNum (z : ByteArray) (i : Nat) : Except Nat (Nat × J × Bool) :=
  let c := bAt z i
  let fuel := z.size + 3
  let fin (j t : Nat) (ns : Bool) : Except Nat (Nat × J × Bool) :=
    let a := if bAt z i == 43 then i + 1 else i
    let raw := z.extract a j
    let node : J :=
      if t == 0 then .int raw
      else if t == 2 then .flt raw
      else if t == 1 then .lit raw (hexInt5 raw)
      else .lit raw (.flt (float5Text raw))
    .ok (j, node, ns || (t &&& 1) != 0)
  let viaLoop (j0 t : Nat) (ns : Bool) : Except Nat (Nat × J × Bool) :=
    match numLoop z i fuel j0 t false ns with
    | .error p => .error p
    | .ok (j, t, ns) => fin j t ns
  if c == 46 then
    if isDig (bAt z (i + 1)) then viaLoop (i + 1) 3 true else .error i
  else if c == 48 then
    let c1 := bAt z (i + 1)
    if (c1 == 120 || c1 == 88) && isHex (bAt z (i + 2)) then fin (hexEnd z fuel (i + 3)) 1 true
    else if isDig c1 then .error (i + 1)
    else viaLoop (i + 1) 0 false
  else if c == 43 || c == 45 then
    let c1 := bAt z (i + 1)
    if !isDig c1 then
      if (c1 == 105 || c1 == 73) && ciMatch z (i + 1) (bs "inf") then
        let e := i + (if ciMatch z (i + 4) (bs "inity") then 9 else 4)
        .ok (e, .flt (bs (if c == 45 then "-9e999" else "9e999")), true)
      else if c1 == 46 then viaLoop (i + 1) 1 true
      else .error i
    else
      let c2 := bAt z (i + 2)
      if c1 == 48 then
        if isDig c2 then .error (i + 1)
        else if (c2 == 120 || c2 == 88) && isHex (bAt z (i + 3)) then fin (hexEnd z fuel (i + 4)) 1 true
        else viaLoop (i + 1) 0 (c == 43)
      else viaLoop (i + 1) 0 (c == 43)
  else viaLoop (i + 1) 0 false

/-- inf, infinity, nan, qnan, snan (any case), as sqlite accepts them. -/
def namedLit (z : ByteArray) (i : Nat) : Option (Nat × J) :=
  let tab : Array (String × Bool) := #[("inf", true), ("infinity", true), ("nan", false), ("qnan", false), ("snan", false)]
  tab.findSome? fun (nm, fl) =>
    let lit := bs nm
    if ciMatch z i lit && !isAlnum (bAt z (i + lit.size)) then
      some (i + lit.size, if fl then J.flt (bs "9e999") else J.null)
    else none

def isHex2 (z : ByteArray) (i : Nat) : Bool := isHex (bAt z i) && isHex (bAt z (i + 1))

/-- sqlite3JsonId1 / Id2: identifier characters of a JSON5 unquoted key. -/
def isId1 (c : UInt8) : Bool := isAlpha c || c == 95 || c == 36 || c >= 128
def isId2 (c : UInt8) : Bool := isId1 c || isDig c

/-- json5Whitespace: the length of the white space and comments at i. -/
def ws5 (z : ByteArray) (fuel i : Nat) : Nat :=
  match fuel with
  | 0 => 0
  | fuel + 1 =>
    let c := bAt z i
    let step (m : Nat) : Nat := m + ws5 z fuel (i + m)
    if c == 9 || c == 10 || c == 11 || c == 12 || c == 13 || c == 32 then step 1
    else if c == 47 then
      if bAt z (i + 1) == 42 && bAt z (i + 2) != 0 then
        let rec find (j f : Nat) : Option Nat :=
          match f with
          | 0 => none
          | f + 1 =>
            if bAt z j == 0 then none
            else if bAt z j == 47 && bAt z (j - 1) == 42 then some j else find (j + 1) f
        match find (i + 3) (z.size + 2) with
        | some j => step (j + 1 - i)
        | none => 0
      else if bAt z (i + 1) == 47 then
        let rec eol (j f : Nat) : Nat :=
          match f with
          | 0 => j
          | f + 1 =>
            let d := bAt z j
            if d == 0 then j
            else if d == 10 || d == 13 then j
            else if d == 0xe2 && bAt z (j + 1) == 0x80 && (bAt z (j + 2) == 0xa8 || bAt z (j + 2) == 0xa9) then j + 2
            else eol (j + 1) f
        let j := eol (i + 2) (z.size + 2)
        step ((if bAt z j != 0 then j + 1 else j) - i)
      else 0
    else if c == 0xc2 then (if bAt z (i + 1) == 0xa0 then step 2 else 0)
    else if c == 0xe1 then (if bAt z (i + 1) == 0x9a && bAt z (i + 2) == 0x80 then step 3 else 0)
    else if c == 0xe2 then
      if bAt z (i + 1) == 0x80 then
        let d := bAt z (i + 2)
        if d >= 0x80 && (d <= 0x8a || d == 0xa8 || d == 0xa9 || d == 0xaf) then step 3 else 0
      else if bAt z (i + 1) == 0x81 && bAt z (i + 2) == 0x9f then step 3
      else 0
    else if c == 0xe3 then (if bAt z (i + 1) == 0x80 && bAt z (i + 2) == 0x80 then step 3 else 0)
    else if c == 0xef then (if bAt z (i + 1) == 0xbb && bAt z (i + 2) == 0xbf then step 3 else 0)
    else 0

def ws5At (z : ByteArray) (i : Nat) : Nat := ws5 z (z.size + 2) i

def idEnd (z : ByteArray) (fuel k : Nat) : Nat :=
  match fuel with
  | 0 => k
  | fuel + 1 => if isId2 (bAt z k) && ws5At z k == 0 then idEnd z fuel (k + 1) else k

/-- A string literal's body from j to the closing delimiter: (position of the delimiter, has escape, needs translation). -/
def strLoop (z : ByteArray) (fuel j : Nat) (delim : UInt8) (esc t5 : Bool) : Except Nat (Nat × Bool × Bool) :=
  match fuel with
  | 0 => .error j
  | fuel + 1 =>
    let c := bAt z j
    if c == delim then .ok (j, esc, t5)
    else if c == 92 then
      let c2 := bAt z (j + 1)
      if c2 == 34 || c2 == 92 || c2 == 47 || c2 == 98 || c2 == 102 || c2 == 110 || c2 == 114 || c2 == 116 then
        strLoop z fuel (j + 2) delim true t5
      else if c2 == 117 && isHex4 z (j + 2) then strLoop z fuel (j + 6) delim true t5
      else if c2 == 39 || c2 == 118 || c2 == 10 || (c2 == 48 && !isDig (bAt z (j + 2)))
          || (c2 == 0xe2 && bAt z (j + 2) == 0x80 && (bAt z (j + 3) == 0xa8 || bAt z (j + 3) == 0xa9))
          || (c2 == 120 && isHex2 z (j + 2)) then
        strLoop z fuel (j + 2) delim true true
      else if c2 == 13 then strLoop z fuel (j + (if bAt z (j + 2) == 10 then 3 else 2)) delim true true
      else .error (j + 1)
    else if c < 32 then (if c == 0 then .error j else strLoop z fuel (j + 1) delim esc true)
    else if c == 34 then strLoop z fuel (j + 1) delim esc true
    else strLoop z fuel (j + 1) delim esc t5

def pstr (z : ByteArray) (i : Nat) (delim : UInt8) : PR :=
  match strLoop z (z.size + 3) (i + 1) delim false false with
  | .error p => .fail p
  | .ok (j, esc, t5) => .val (j + 1) (.str { raw := z.extract (i + 1) j, esc := esc, t5 := t5 }) (t5 || delim == 39) none

/-- A JSON5 unquoted label at j (after white space): its end and string. -/
def idLabel (z : ByteArray) (j : Nat) : Option (Nat × Str) :=
  let j := j + ws5At z j
  if isId1 (bAt z j) then
    let k := idEnd z (z.size + 2) (j + 1)
    some (k, { raw := z.extract j k })
  else none

mutual
def pv (z : ByteArray) (fuel depth i : Nat) : PR :=
  match fuel with
  | 0 => .fail i
  | fuel + 1 =>
    let c := bAt z i
    if c == 123 then
      if depth + 1 > maxDepth then .fail i else pobj z fuel (depth + 1) (i + 1) #[] 0 false none
    else if c == 91 then
      if depth + 1 > maxDepth then .fail i else parr z fuel (depth + 1) (i + 1) #[] 0 false none
    else if c == 34 then pstr z i 34
    else if c == 39 then pstr z i 39
    else if isSp c then pv z fuel depth (skipWs z (i + 1))
    else if c == 0 then .tok 0 0
    else if c == 125 then .tok 2 i
    else if c == 93 then .tok 3 i
    else if c == 44 then .tok 4 i
    else if c == 58 then .tok 5 i
    else if c == 11 || c == 12 || c == 47 || c == 0xc2 || c == 0xe1 || c == 0xe2 || c == 0xe3 || c == 0xef then
      let w := ws5At z i
      if w > 0 then
        match pv z fuel depth (i + w) with
        | .val e j _ ie => .val e j true ie
        | r => r
      else .fail i
    else if c == 116 then
      if litAt z i (bs "true") && !isAlnum (bAt z (i + 4)) then .val (i + 4) .tru false none else .fail i
    else if c == 102 then
      if litAt z i (bs "false") && !isAlnum (bAt z (i + 5)) then .val (i + 5) .fls false none else .fail i
    else if c == 110 && litAt z i (bs "null") && !isAlnum (bAt z (i + 4)) then .val (i + 4) .null false none
    else if c == 45 || c == 43 || c == 46 || isDig c then
      match parseNum z i with
      | .ok (e, j, ns) => .val e j ns none
      | .error p => .fail p
    else
      match namedLit z i with
      | some (e, j) => .val e j true none
      | none => .fail i

/-- After a value ending at e in an array: the separator, then the next element or the end. -/
def parr (z : ByteArray) (fuel depth j : Nat) (acc : Array J) (sz : Nat) (ns : Bool) (ie : Option Nat) : PR :=
  match fuel with
  | 0 => .fail j
  | fuel + 1 =>
    match pv z fuel depth j with
    | .tok 3 p => .val (p + 1) (.arr acc sz) (ns || !acc.isEmpty) (some p)
    | .tok _ _ => .fail j
    | .fail p => .fail p
    | .val e x ns' ie' =>
      let acc := acc.push x
      let sz := sz + x.size
      let ns := ns || ns'
      let ie := ie'.orElse fun _ => ie
      let c := bAt z e
      if c == 44 then parr z fuel depth (e + 1) acc sz ns ie
      else if c == 93 then .val (e + 1) (.arr acc sz) ns ie
      else
        let e2 := if isSp c then skipWs z (e + 1) else e
        let c2 := bAt z e2
        if c2 == 44 then parr z fuel depth (e2 + 1) acc sz ns ie
        else if c2 == 93 then .val (e2 + 1) (.arr acc sz) ns ie
        else
          match pv z fuel depth e2 with
          | .tok 4 p => parr z fuel depth (p + 1) acc sz true (some p)
          | .tok 3 p => .val (p + 1) (.arr acc sz) true (some p)
          | _ => .fail e2

def pobj (z : ByteArray) (fuel depth j : Nat) (acc : Array (Str × J)) (sz : Nat) (ns : Bool) (ie : Option Nat) : PR :=
  match fuel with
  | 0 => .fail j
  | fuel + 1 =>
    let withLabel (e : Nat) (s : Str) (ns : Bool) : PR :=
      let c := bAt z e
      let e2 := if isSp c then skipWs z (e + 1) else e
      if bAt z e2 == 58 then pobjVal z fuel depth (e2 + 1) acc sz ns ie s
      else
        match pv z fuel depth e2 with
        | .fail p => .fail p
        | .tok 5 p => pobjVal z fuel depth (p + 1) acc sz true ie s
        | _ => .fail e2
    match pv z fuel depth j with
    | .tok 2 p => .val (p + 1) (.obj acc sz) (ns || !acc.isEmpty) (some p)
    | .val e (.str s) nsl _ => withLabel e s (ns || nsl)
    | .val _ _ _ _ => .fail j
    | r =>
      match idLabel z j with
      | some (k, s) => withLabel k s true
      | none =>
        match r with
        | .fail p => .fail p
        | _ => .fail j

def pobjVal (z : ByteArray) (fuel depth j : Nat) (acc : Array (Str × J)) (sz : Nat) (ns : Bool) (ie : Option Nat) (s : Str) : PR :=
  match fuel with
  | 0 => .fail j
  | fuel + 1 =>
    match pv z fuel depth j with
    | .tok _ _ => .fail j
    | .fail p => .fail p
    | .val e x nsx ie' =>
      let acc := acc.push (s, x)
      let sz := sz + s.size + x.size
      let ns := ns || nsx
      let ie := ie'.orElse fun _ => ie
      let c := bAt z e
      if c == 44 then pobj z fuel depth (e + 1) acc sz ns ie
      else if c == 125 then .val (e + 1) (.obj acc sz) ns ie
      else
        let e2 := if isSp c then skipWs z (e + 1) else e
        let c2 := bAt z e2
        if c2 == 44 then pobj z fuel depth (e2 + 1) acc sz ns ie
        else if c2 == 125 then .val (e2 + 1) (.obj acc sz) ns ie
        else
          match pv z fuel depth e2 with
          | .tok 4 p => pobj z fuel depth (p + 1) acc sz true (some p)
          | .tok 2 p => .val (p + 1) (.obj acc sz) true (some p)
          | _ => .fail e2
end

/-- Parse a whole text: the tree and whether it used anything beyond RFC 8259, or sqlite's iErr (a byte offset). -/
def parseDoc (z : ByteArray) : Except Nat (J × Bool) :=
  match pv z (z.size + 3) 0 0 with
  | .val e j ns ie =>
    let e2 := skipWs z e
    if bAt z e2 == 0 then .ok (j, ns)
    else
      let w := ws5At z e2
      if bAt z (e2 + w) == 0 then .ok (j, true) else .error (ie.getD 0)
  | .tok _ p => .error p
  | .fail p => .error p

/-! ### JSONB (a BLOB that holds sqlite's binary JSON) -/

/-- The header of the JSONB element at i: (header size, payload size). -/
def jbHdr (b : ByteArray) (i : Nat) : Option (Nat × Nat) :=
  let s := (bAt b i >>> 4).toNat
  let be (k : Nat) : Nat := Id.run do
    let mut v := 0
    for m in [0:k] do
      v := v * 256 + (bAt b (i + 1 + m)).toNat
    return v
  if s <= 11 then some (1, s)
  else if s == 12 then (if i + 2 <= b.size then some (2, be 1) else none)
  else if s == 13 then (if i + 3 <= b.size then some (3, be 2) else none)
  else if s == 14 then (if i + 5 <= b.size then some (5, be 4) else none)
  else (if i + 9 <= b.size then some (9, be 8) else none)

mutual
def jbDecode (b : ByteArray) (fuel i : Nat) : Option (J × Nat) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    if i >= b.size then none else
    match jbHdr b i with
    | none => none
    | some (n, sz) =>
      let st := i + n
      let en := st + sz
      let t := bAt b i &&& 15
      if en > b.size then none
      else if t == 0 then (if sz == 0 then some (.null, en) else none)
      else if t == 1 then (if sz == 0 then some (.tru, en) else none)
      else if t == 2 then (if sz == 0 then some (.fls, en) else none)
      else if t == 3 then
        (match convertInteger (b.extract st en) with | .bad => none | _ => some (.int (b.extract st en), en))
      else if t == 4 then
        (match convertInteger (b.extract st en) with
          | .bad => none
          | _ => some (.lit (b.extract st en) (hexInt5 (b.extract st en)), en))
      else if t == 5 then (if sz > 0 then some (.flt (b.extract st en), en) else none)
      else if t == 6 then (if sz > 0 then some (.lit (b.extract st en) (.flt (float5Text (b.extract st en))), en) else none)
      else if t == 7 then some (.str { raw := b.extract st en }, en)
      else if t == 8 then some (.str { raw := b.extract st en, esc := true }, en)
      else if t == 9 then some (.str { raw := b.extract st en, esc := true, t5 := true }, en)
      else if t == 10 then some (.str (quoteStr (b.extract st en)), en)
      else if t == 11 then
        (match jbElems b fuel st en #[] with
          | some xs => some (mkArr xs, en)
          | none => none)
      else if t == 12 then
        (match jbPairs b fuel st en #[] with
          | some kvs => some (mkObj kvs, en)
          | none => none)
      else none

def jbElems (b : ByteArray) (fuel j en : Nat) (acc : Array J) : Option (Array J) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    if j >= en then some acc
    else
      match jbDecode b fuel j with
      | some (x, nx) => if nx > en then none else jbElems b fuel nx en (acc.push x)
      | none => none

def jbPairs (b : ByteArray) (fuel j en : Nat) (acc : Array (Str × J)) : Option (Array (Str × J)) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    if j >= en then some acc
    else
      match jbDecode b fuel j with
      | some (.str s, nx) =>
        if nx >= en then none else
        match jbDecode b fuel nx with
        | some (x, ny) => if ny > en then none else jbPairs b fuel ny en (acc.push (s, x))
        | none => none
      | _ => none
end

/-- jsonArgIsJsonb: the BLOB is a JSONB value. -/
def asJsonb (b : ByteArray) : Option J :=
  match jbDecode b (b.size + 2) 0 with
  | some (j, e) => if e == b.size then some j else none
  | none => none

/-! ### Paths (jsonLookupStep) -/

inductive LErr where
  | error | notFound | notArray | tooDeep | pathError
  deriving DecidableEq

def scanQuoted (z : ByteArray) (k fuel : Nat) : Option Nat :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    let c := bAt z k
    if c == 0 then none
    else if c == 34 then some k
    else if c == 92 && bAt z (k + 1) != 0 then scanQuoted z (k + 2) fuel
    else scanQuoted z (k + 1) fuel

def scanBare (z : ByteArray) (k fuel : Nat) : Nat :=
  match fuel with
  | 0 => k
  | fuel + 1 =>
    let c := bAt z k
    if c == 0 || c == 46 || c == 91 then k else scanBare z (k + 1) fuel

/-- The key after a '.' at q: (key start, key length, escape free, position after it). -/
def parseKey (z : ByteArray) (q : Nat) : Except LErr (Nat × Nat × Bool × Nat) :=
  if bAt z q == 34 then
    match scanQuoted z (q + 1) (z.size + 2) with
    | none => .error .pathError
    | some k => .ok (q + 1, k - (q + 1), findByte z 92 (q + 1) >= k, k + 1)
  else
    let k := scanBare z q (z.size + 2)
    if k == q then .error .pathError else .ok (q, k - q, true, k)

def digitsFrom (z : ByteArray) (fuel k kk : Nat) : Nat × Nat :=
  match fuel with
  | 0 => (k, kk)
  | fuel + 1 =>
    let c := bAt z k
    if isDig c then digitsFrom z fuel (k + 1) (if kk < 0xffffffff then kk * 10 + (c - 48).toNat else kk)
    else (k, kk)

/-- The index after a '[' at p, in an array of count elements: (index, position of the ']'). -/
def parseIdx (z : ByteArray) (p count : Nat) : Except LErr (Nat × Nat) :=
  let (k, kk) := digitsFrom z (z.size + 2) (p + 1) 0
  if k >= p + 2 && bAt z k == 93 then .ok (kk, k)
  else if bAt z (p + 1) == 35 then
    if bAt z (p + 2) == 45 && isDig (bAt z (p + 3)) then
      let (k2, nn) := digitsFrom z (z.size + 2) (p + 3) 0
      if nn > count then .error .notFound
      else if bAt z k2 == 93 then .ok (count - nn, k2) else .error .pathError
    else if bAt z (p + 2) == 93 then .ok (count, p + 2) else .error .pathError
  else .error .pathError

def findKey (kvs : Array (Str × J)) (key : ByteArray) (raw : Bool) : Option Nat := Id.run do
  let ks : Str := { raw := key, esc := !raw }
  for i in [0:kvs.size] do
    match kvs[i]? with
    | some (k, _) => if labelEq ks k then return some i
    | none => pure ()
  return none

structure Hit where
  node : J
  /-- JSONB offset of the node (only when tracked). -/
  off : Nat := 0
  /-- JSONB offset of its label when it is an object member, else 0. -/
  lab : Nat := 0

def objEntryOffs (kvs : Array (Str × J)) (idx start : Nat) : Nat × Nat := Id.run do
  let mut o := start
  for i in [0:idx] do
    match kvs[i]? with
    | some (k, v) => o := o + k.size + v.size
    | none => pure ()
  match kvs[idx]? with
  | some (k, _) => return (o + k.size, o)
  | none => return (o, o)

def arrElemOff (xs : Array J) (idx start : Nat) : Nat := Id.run do
  let mut o := start
  for i in [0:idx] do
    match xs[i]? with
    | some v => o := o + v.size
    | none => pure ()
  return o

def lookStep (z : ByteArray) (track : Bool) (fuel depth : Nat) (j : J) (off lab p : Nat) : Except LErr Hit :=
  match fuel with
  | 0 => .error .tooDeep
  | fuel + 1 =>
    let c := bAt z p
    if c == 0 then .ok { node := j, off := off, lab := lab }
    else if c == 46 then
      match parseKey z (p + 1) with
      | .error e => .error e
      | .ok (ks, nk, raw, nxt) =>
        match j with
        | .obj kvs sz =>
          match findKey kvs (z.extract ks (ks + nk)) raw with
          | none => .error .notFound
          | some idx =>
            match kvs[idx]? with
            | none => .error .error
            | some (_, v) =>
              if depth + 1 >= maxDepth then .error .tooDeep else
              let (vo, lo) := if track then objEntryOffs kvs idx (off + hdrSize sz) else (0, 0)
              lookStep z track fuel (depth + 1) v vo lo nxt
        | _ => .error .notFound
    else if c == 91 then
      match j with
      | .arr xs sz =>
        match parseIdx z p xs.size with
        | .error e => .error e
        | .ok (kk, k) =>
          match xs[kk]? with
          | none => .error .notFound
          | some v =>
            if depth + 1 >= maxDepth then .error .tooDeep else
            lookStep z track fuel (depth + 1) v (if track then arrElemOff xs kk (off + hdrSize sz) else 0) 0 (k + 1)
      | _ => .error .notFound
    else .error .pathError

inductive Mode where
  | del | repl | ins | set | ains
  deriving DecidableEq

def Mode.creates : Mode → Bool
  | .ins | .set | .ains => true
  | _ => false

/-- What an edit does to the node it reached: leave it, replace it, delete it, or insert before it. -/
inductive R where
  | keep
  | repl (j : J)
  | del
  | insBefore (j : J)

def keyStr (key : ByteArray) (raw : Bool) : Str :=
  if raw then quoteStr key else { raw := key, esc := true, t5 := true }

def removeAt (xs : Array α) (i : Nat) : Array α := xs.extract 0 i ++ xs.extract (i + 1) xs.size
def insertAt (xs : Array α) (i : Nat) (v : α) : Array α := xs.extract 0 i ++ #[v] ++ xs.extract i xs.size

mutual
def editStep (z : ByteArray) (mode : Mode) (v : J) (fuel depth : Nat) (j : J) (member : Bool) (p : Nat) : Except LErr R :=
  match fuel with
  | 0 => .error .tooDeep
  | fuel + 1 =>
    let c := bAt z p
    if c == 0 then
      match mode with
      | .del => .ok .del
      | .ins => .ok .keep
      | .ains => if bAt z (p - 1) != 93 || member then .error .notArray else .ok (.insBefore v)
      | .repl | .set => .ok (.repl v)
    else if c == 46 then
      match parseKey z (p + 1) with
      | .error e => .error e
      | .ok (ks, nk, raw, nxt) =>
        match j with
        | .obj kvs _ =>
          let key := z.extract ks (ks + nk)
          match findKey kvs key raw with
          | some idx =>
            match kvs[idx]? with
            | none => .error .error
            | some (k, ch) =>
              if depth + 1 >= maxDepth then .error .tooDeep else
              match editStep z mode v fuel (depth + 1) ch true nxt with
              | .error e => .error e
              | .ok .keep => .ok .keep
              | .ok (.repl c') => .ok (.repl (mkObj (kvs.setIfInBounds idx (k, c'))))
              | .ok .del => .ok (.repl (mkObj (removeAt kvs idx)))
              | .ok (.insBefore _) => .ok .keep
          | none =>
            if !mode.creates then .error .notFound
            else if mode == .ains && !(nxt < z.size && bAt z (z.size - 1) == 93) then .error .notArray
            else
              match createSub z mode v fuel depth nxt with
              | .error e => .error e
              | .ok ch => .ok (.repl (mkObj (kvs.push (keyStr key raw, ch))))
        | _ => .error .notFound
    else if c == 91 then
      match j with
      | .arr xs _ =>
        match parseIdx z p xs.size with
        | .error e => .error e
        | .ok (kk, k) =>
          match xs[kk]? with
          | some ch =>
            if depth + 1 >= maxDepth then .error .tooDeep else
            match editStep z mode v fuel (depth + 1) ch false (k + 1) with
            | .error e => .error e
            | .ok .keep => .ok .keep
            | .ok (.repl c') => .ok (.repl (mkArr (xs.setIfInBounds kk c')))
            | .ok .del => .ok (.repl (mkArr (removeAt xs kk)))
            | .ok (.insBefore w) => .ok (.repl (mkArr (insertAt xs kk w)))
          | none =>
            if kk == xs.size && mode.creates then
              match createSub z mode v fuel depth (k + 1) with
              | .error e => .error e
              | .ok ch => .ok (.repl (mkArr (xs.push ch)))
            else .error .notFound
      | _ => .error .notFound
    else .error .pathError

/-- jsonCreateEditSubstructure: the value to insert for the rest of the path at p. -/
def createSub (z : ByteArray) (mode : Mode) (v : J) (fuel depth : Nat) (p : Nat) : Except LErr J :=
  match fuel with
  | 0 => .error .tooDeep
  | fuel + 1 =>
    if bAt z p == 0 then .ok v
    else if depth + 1 >= maxDepth then .error .tooDeep
    else
      let empty : J := if bAt z p == 46 then .obj #[] 0 else .arr #[] 0
      match editStep z mode v fuel (depth + 1) empty false p with
      | .error e => .error e
      | .ok (.repl c') => .ok c'
      | .ok _ => .ok empty
end


/-! ### SQL values and JSON -/

def floatBytes (f : Float) : ByteArray :=
  if f != f then bs "null"
  else if f == Num.posInf then bs "9.0e+999"
  else if f == -Num.posInf then bs "-9.0e+999"
  else Num.fmtRealBytes f

/-- jsonAppendSqlValue: a SQL value as JSON text. isJ: the value came from a JSON function, so its text is JSON. -/
def appendSqlValue (o : ByteArray) (v : Value) (isJ : Bool) : Except String ByteArray :=
  match v with
  | .null => .ok (ByteArray.append o (bs "null"))
  | .real f => .ok (ByteArray.append o (floatBytes f))
  | .int i => .ok (ByteArray.append o (Num.int64ToBytes i))
  | .text s => if isJ then .ok (ByteArray.append o s.toUTF8) else .ok (appendQuoted o s.toUTF8)
  | .blob b =>
    match asJsonb b with
    | some j => .ok (ByteArray.append o (render j))
    | none => .error "JSON cannot hold BLOB values"

/-- jsonFunctionArgToBlob: a SQL value as a node (the value argument of json_set and friends). -/
def argToJ (v : Value) (isJ : Bool) : Except String J :=
  match v with
  | .null => .ok .null
  | .blob b =>
    match asJsonb b with
    | some j => .ok j
    | none => .error "JSON cannot hold BLOB values"
  | .text s =>
    if isJ then
      match parseDoc s.toUTF8 with
      | .ok (j, _) => .ok j
      | .error _ => .error "malformed JSON"
    else .ok (.str (quoteStr s.toUTF8))
  | .int i => .ok (.int (Num.int64ToBytes i))
  | .real f =>
    if f != f then .ok .null
    else if f == Num.posInf then .ok (.flt (bs "9e999"))
    else if f == -Num.posInf then .ok (.flt (bs "-9e999"))
    else .ok (.flt (Num.fmtRealBytes f))

/-- jsonParseFuncArg: none for NULL, an error for text that is not JSON. -/
def docArg (v : Value) : Except String (Option J) :=
  match v with
  | .null => .ok none
  | _ =>
    let b := v.toBytes
    match (match v with | .blob bb => asJsonb bb | _ => none) with
    | some j => .ok (some j)
    | none =>
    if b.size == 0 then .error "malformed JSON"
    else
      match parseDoc b with
      | .ok (j, _) => .ok (some j)
      | .error _ => .error "malformed JSON"

/-- jsonReturnFromBlob: the SQL value of a node (arrays and objects as their JSON text). -/
def toSql (j : J) : Except String Value :=
  match j with
  | .null => .ok .null
  | .tru => .ok (.int 1)
  | .fls => .ok (.int 0)
  | .int raw =>
    match convertInteger raw with
    | .i v => .ok (.int v)
    | .r _ => .ok (.real (Num.atoFBytes raw).value)
    | .bad => .error "malformed JSON"
  | .flt raw =>
    let r := Num.atoFBytes raw
    if r.rc <= 0 then .error "malformed JSON" else .ok (.real r.value)
  | .str s => .ok (.text (Num.bytesToString s.bytes))
  | .arr .. | .obj .. => .ok (.text (Num.bytesToString (render j)))
  | .lit orig c =>
    if bAt orig (if bAt orig 0 == 45 then 1 else 0) == 48 && (bAt orig (if bAt orig 0 == 45 then 2 else 1) == 120 || bAt orig (if bAt orig 0 == 45 then 2 else 1) == 88) then
      let neg := bAt orig 0 == 45
      let u := hexLitVal orig
      if u >= 18446744073709551616 then .error "malformed JSON"
      else if u > 9223372036854775807 then .ok (.real (if neg then -(Float.ofNat u) else Float.ofNat u))
      else .ok (.int (if neg then 0 - Int64.ofNat u else Int64.ofNat u))
    else
      match c with
      | .flt raw =>
        let r := Num.atoFBytes raw
        if r.rc <= 0 then .error "malformed JSON" else .ok (.real r.value)
      | _ => .error "malformed JSON"

def quoteQ (s : String) : String := "'" ++ s.replace "'" "''" ++ "'"

/-- jsonBadPathError. -/
def badPath (path : String) (e : LErr) : String :=
  match e with
  | .notArray => "not an array element: " ++ quoteQ path
  | .error => "malformed JSON"
  | .tooDeep => "JSON path too deep"
  | _ => "bad JSON path: " ++ quoteQ path

abbrev Res := Except String (Value × Bool)

def textV (b : ByteArray) : Value := .text (Num.bytesToString b)

def fuel0 : Nat := maxDepth + 2

def allAlnum (b : ByteArray) : Bool := Id.run do
  for c in b do
    if !(isAlnum c || c == 95) then return false
  return true

/-- The path -> and ->> build from a bare key or an index. -/
def abPath (v : Value) (z : ByteArray) : ByteArray :=
  match v with
  | .int _ => if bAt z 0 == 45 then ByteArray.append (ByteArray.append (bs "[#") z) (bs "]") else ByteArray.append (ByteArray.append (bs "[") z) (bs "]")
  | _ =>
    if allAlnum z then ByteArray.append (bs ".") z
    else if bAt z 0 == 91 && z.size >= 3 && bAt z (z.size - 1) == 93 then z
    else ByteArray.append (ByteArray.append (bs ".\"") z) (bs "\"")

/-- A path argument as bytes (up to a NUL). -/
def pathOf (v : Value) : ByteArray := Num.cstr v.toBytes

/-- jsonExtractFunc. jsonMode: -> ; sqlMode: ->> ; abpath: accept bare keys and indexes. -/
def extractFn (args : Array Value) (jsonMode sqlMode abpath : Bool) : Res := do
  if args.size < 2 then return (.null, false)
  let some doc ← docArg (args.getD 0 .null) | return (.null, false)
  let mut out : ByteArray := ByteArray.empty.push 91
  let mut single : Value × Bool := (.null, false)
  for i in [1:args.size] do
    let pv := args.getD i .null
    if pv.isNull then return (.null, false)
    let zp := pathOf pv
    let hit : Except LErr Hit :=
      if bAt zp 0 == 36 then lookStep zp false fuel0 0 doc 0 0 1
      else if abpath then lookStep (abPath pv zp) false fuel0 0 doc 0 0 0
      else .error .pathError
    match hit with
    | .ok h =>
      if args.size == 2 then
        if jsonMode then single := (textV (render h.node), true)
        else single := (← toSql h.node, h.node.isContainer && !sqlMode)
      else
        if i > 1 then out := out.push 44
        out := renderJ fuel0 h.node out
    | .error .notFound =>
      if args.size == 2 then return (.null, false)
      if i > 1 then out := out.push 44
      out := ByteArray.append out (bs "null")
    | .error e => throw (badPath pv.toText e)
  if args.size == 2 then return single
  return (textV (out.push 93), true)

/-- json_set, json_insert, json_replace, json_array_insert. -/
def editFn (mode : Mode) (args : Array Value) (isJ : Array Bool) : Res := do
  let some doc ← docArg (args.getD 0 .null) | return (.null, false)
  let mut root := doc
  for i in [1:args.size:2] do
    let pv := args.getD i .null
    if pv.isNull then continue
    let zp := pathOf pv
    if bAt zp 0 != 36 then throw (badPath pv.toText .pathError)
    let nv ← argToJ (args.getD (i + 1) .null) (isJ.getD (i + 1) false)
    if bAt zp 1 == 0 then
      match mode with
      | .repl | .set => root := nv
      | _ => pure ()
    else
      match editStep zp mode nv fuel0 0 root false 1 with
      | .ok (.repl r) => root := r
      | .ok _ => pure ()
      | .error .notFound => pure ()
      | .error e => throw (badPath pv.toText e)
  return (textV (render root), true)

def removeFn (args : Array Value) : Res := do
  let some doc ← docArg (args.getD 0 .null) | return (.null, false)
  let mut root := doc
  for i in [1:args.size] do
    let pv := args.getD i .null
    if pv.isNull then return (.null, false)
    let zp := pathOf pv
    if bAt zp 0 != 36 then throw (badPath pv.toText .pathError)
    if bAt zp 1 == 0 then return (.null, false)
    match editStep zp .del .null fuel0 0 root false 1 with
    | .ok (.repl r) => root := r
    | .ok _ => pure ()
    | .error .notFound => pure ()
    | .error e => throw (badPath pv.toText e)
  return (textV (render root), true)

def findLabel (t : Array (Str × J)) (s : Str) : Option Nat := Id.run do
  for i in [0:t.size] do
    match t[i]? with
    | some (k, _) => if labelEq s k then return some i
    | none => pure ()
  return none

/-- RFC 7396 MergePatch (jsonMergePatch). -/
def mergePatch (fuel depth : Nat) (target patch : J) : Except String J :=
  match fuel with
  | 0 => .error "JSON nested too deep"
  | fuel + 1 =>
    match patch with
    | .obj pkvs _ => do
      let mut t : Array (Str × J) := match target with | .obj t _ => t | _ => #[]
      for (pk, pv) in pkvs do
        match findLabel t pk with
        | some idx =>
          match pv with
          | .null => t := removeAt t idx
          | _ =>
            match t[idx]? with
            | some (k, tv) =>
              if depth >= maxDepth then throw "JSON nested too deep"
              let nv ← mergePatch fuel (depth + 1) tv pv
              t := t.setIfInBounds idx (k, nv)
            | none => pure ()
        | none =>
          match pv with
          | .null => pure ()
          | .obj .. =>
            if depth >= maxDepth then throw "JSON nested too deep"
            let nv ← mergePatch fuel (depth + 1) (.obj #[] 0) pv
            t := t.push (pk, nv)
          | _ => t := t.push (pk, pv)
      return mkObj t
    | _ => .ok patch

/-- Path lookup for json_type and json_array_length: none when not found (a NULL result). -/
def lookupArg (doc : J) (pv : Value) : Except String (Option J) :=
  let zp := pathOf pv
  if bAt zp 0 != 36 then .error (badPath pv.toText .pathError)
  else
    match lookStep zp false fuel0 0 doc 0 0 1 with
    | .ok h => .ok (some h.node)
    | .error .notFound => .ok none
    | .error e => .error (badPath pv.toText e)

def errPos (z : ByteArray) (iErr : Nat) : Nat := Id.run do
  let mut n := 0
  for k in [0:iErr] do
    let c := bAt z k
    if c == 0 then return n + 1
    if (c &&& 0xc0) != 0x80 then n := n + 1
  return n + 1

def arityOk (name : String) (n : Nat) : Bool :=
  match name with
  | "JSON" | "JSON_QUOTE" | "JSON_ERROR_POSITION" => n == 1
  | "JSON_ARRAY_LENGTH" | "JSON_TYPE" | "JSON_VALID" | "JSON_PRETTY" => n == 1 || n == 2
  | "JSON_PATCH" | "->" | "->>" => n == 2
  | _ => true

def isJsonFn (name : String) : Bool :=
  match name with
  | "JSON" | "JSON_ARRAY" | "JSON_ARRAY_LENGTH" | "JSON_EXTRACT" | "JSON_INSERT" | "JSON_REPLACE" | "JSON_SET"
  | "JSON_REMOVE" | "JSON_OBJECT" | "JSON_PATCH" | "JSON_QUOTE" | "JSON_TYPE" | "JSON_VALID"
  | "JSON_ERROR_POSITION" | "JSON_PRETTY" | "JSON_ARRAY_INSERT" | "->" | "->>" => true
  | _ => false

def insName (name : String) : String :=
  if name == "JSON_INSERT" then "insert" else if name == "JSON_REPLACE" then "replace"
  else if name == "JSON_SET" then "set" else "array_insert"

def insMode (name : String) : Mode :=
  if name == "JSON_INSERT" then .ins else if name == "JSON_REPLACE" then .repl
  else if name == "JSON_SET" then .set else .ains

def int64OfNat (n : Nat) : Value := .int (Int64.ofNat n)

/-- The scalar JSON function name (upper case) on args. isJson: which arguments are the direct result of a JSON
function. The second component of the result says the result is JSON text (sqlite's JSON subtype). -/
def callJ (name : String) (args : Array Value) (isJson : Array Bool) : Res :=
  if !arityOk name args.size then
    .error ("wrong number of arguments to function " ++ name.toLower ++ "()")
  else
  let a0 := args.getD 0 .null
  match name with
  | "JSON" => do
    match ← docArg a0 with
    | none => return (.null, false)
    | some j => return (textV (render j), true)
  | "JSON_QUOTE" => do
    let o ← appendSqlValue ByteArray.empty a0 (isJson.getD 0 false)
    return (textV o, true)
  | "JSON_ARRAY" => do
    let mut o : ByteArray := ByteArray.empty.push 91
    for i in [0:args.size] do
      if i > 0 then o := o.push 44
      o ← appendSqlValue o (args.getD i .null) (isJson.getD i false)
    return (textV (o.push 93), true)
  | "JSON_OBJECT" => do
    if args.size % 2 == 1 then throw "json_object() requires an even number of arguments"
    let mut o : ByteArray := ByteArray.empty.push 123
    for i in [0:args.size:2] do
      match args.getD i .null with
      | .text s =>
        if i > 0 then o := o.push 44
        o := (appendQuoted o s.toUTF8).push 58
        o ← appendSqlValue o (args.getD (i + 1) .null) (isJson.getD (i + 1) false)
      | _ => throw "json_object() labels must be TEXT"
    return (textV (o.push 125), true)
  | "JSON_ARRAY_LENGTH" => do
    let some doc ← docArg a0 | return (.null, false)
    if args.size == 2 then
      let pv := args.getD 1 .null
      if pv.isNull then return (.null, false)
      match ← lookupArg doc pv with
      | none => return (.null, false)
      | some (.arr xs _) => return (int64OfNat xs.size, false)
      | some _ => return (.int 0, false)
    else
      match doc with
      | .arr xs _ => return (int64OfNat xs.size, false)
      | _ => return (.int 0, false)
  | "JSON_TYPE" => do
    let some doc ← docArg a0 | return (.null, false)
    if args.size == 2 then
      let pv := args.getD 1 .null
      if pv.isNull then return (.null, false)
      match ← lookupArg doc pv with
      | none => return (.null, false)
      | some j => return (.text j.typeName, false)
    else return (.text doc.typeName, false)
  | "JSON_VALID" => do
    if a0.isNull then return (.null, false)
    let mut flags : Int64 := 1
    if args.size == 2 then
      flags := Num.castToInt (args.getD 1 .null)
      if flags < 1 || flags > 15 then throw "FLAGS parameter to json_valid() must be between 1 and 15"
    let f := flags.toNatClampNeg
    if let .blob bb := a0 then
      if (asJsonb bb).isSome then return (.int (if (f &&& 12) != 0 then 1 else 0), false)
    if (f &&& 3) == 0 then return (.int 0, false)
    let b := a0.toBytes
    if b.size == 0 then return (.int 0, false)
    match parseDoc b with
    | .ok (_, ns) => return (.int (if (f &&& 2) != 0 || !ns then 1 else 0), false)
    | .error _ => return (.int 0, false)
  | "JSON_ERROR_POSITION" => do
    if a0.isNull then return (.null, false)
    if let .blob bb := a0 then
      if (asJsonb bb).isSome then return (.int 0, false)
    let b := a0.toBytes
    match parseDoc b with
    | .ok _ => return (.int 0, false)
    | .error p => return (int64OfNat (errPos b p), false)
  | "JSON_PRETTY" => do
    let some doc ← docArg a0 | return (.null, false)
    let ind : ByteArray :=
      match args.getD 1 .null with
      | .null => bs "    "
      | v => Num.cstr v.toBytes
    return (textV (prettyJ fuel0 ind 0 doc ByteArray.empty), false)
  | "JSON_EXTRACT" => extractFn args false false false
  | "->" => extractFn args true false true
  | "->>" => extractFn args false true true
  | "JSON_INSERT" | "JSON_REPLACE" | "JSON_SET" | "JSON_ARRAY_INSERT" => do
    if args.size == 0 then return (.null, false)
    if args.size % 2 == 0 then throw ("json_" ++ insName name ++ "() needs an odd number of arguments")
    editFn (insMode name) args isJson
  | "JSON_REMOVE" => if args.size == 0 then .ok (.null, false) else removeFn args
  | "JSON_PATCH" => do
    let some t ← docArg a0 | return (.null, false)
    let some p ← docArg (args.getD 1 .null) | return (.null, false)
    let r ← mergePatch (maxDepth + 100) 0 t p
    return (textV (render r), true)
  | _ => .error ("no such function: " ++ name)

def call (name : String) (args : Array Value) (isJson : Array Bool) : Except String Value :=
  (callJ name args isJson).map (·.1)

/-! ### Aggregates -/

/-- The text built so far by json_group_array / json_group_object. -/
structure Agg where
  buf : ByteArray := ByteArray.empty
  err : Option String := none

def isJsonAgg (name : String) : Bool := name == "JSON_GROUP_ARRAY" || name == "JSON_GROUP_OBJECT"

def aggStep (name : String) (acc : Agg) (args : Array Value) (isJson : Array Bool) : Agg :=
  match acc with
  | { buf := buf, err := err } =>
    if err.isSome then { buf := buf, err := err }
    else if name == "JSON_GROUP_ARRAY" then
      let b := if buf.isEmpty then buf.push 91 else buf.push 44
      match appendSqlValue b (args.getD 0 .null) (isJson.getD 0 false) with
      | .ok o => { buf := o, err := none }
      | .error e => { buf := ByteArray.empty, err := some e }
    else
      let b := if buf.isEmpty then buf.push 123 else buf
      match args.getD 0 .null with
      | .null => { buf := b, err := none }
      | k =>
        let b := if b.size > 1 then b.push 44 else b
        let b := (appendQuoted b k.toBytes).push 58
        match appendSqlValue b (args.getD 1 .null) (isJson.getD 1 false) with
        | .ok o => { buf := o, err := none }
        | .error e => { buf := ByteArray.empty, err := some e }

def aggFinal (name : String) (acc : Agg) : Except String Value :=
  match acc.err with
  | some e => .error e
  | none =>
    if acc.buf.isEmpty then .ok (.text (if name == "JSON_GROUP_ARRAY" then "[]" else "{}"))
    else .ok (textV (acc.buf.push (if name == "JSON_GROUP_ARRAY" then 93 else 125)))

/-! ### json_each / json_tree -/

/-- jsonAppendPathName for an object label. -/
def labelPathName (s : Str) : ByteArray := Id.run do
  let z := s.raw
  let mut needQuote := z.size == 0 || !isAlpha (bAt z 0)
  for c in z do
    if !isAlnum c then needQuote := true
  if !needQuote then return (ByteArray.empty.push 46) ++ z
  let mut o : ByteArray := (ByteArray.empty.push 46).push 34
  let mut i := 0
  for _ in [0:z.size] do
    if i >= z.size then break
    let c := bAt z i
    if c == 92 && i + 1 < z.size then
      o := (o.push c).push (bAt z (i + 1))
      i := i + 2
    else
      if c == 34 || c == 92 then o := o.push 92
      o := o.push c
      i := i + 1
  return o.push 34

/-- The children of a container at JSONB offset cOff: (key, path name, node, node offset, row id). -/
def children (c : J) (cOff : Nat) : Array (Value × ByteArray × J × Nat × Nat) := Id.run do
  let mut out := #[]
  match c with
  | .arr xs sz =>
    let mut off := cOff + hdrSize sz
    for idx in [0:xs.size] do
      match xs[idx]? with
      | some ch =>
        let nm := ((ByteArray.empty.push 91) ++ Num.int64ToBytes (Int64.ofNat idx)).push 93
        out := out.push (int64OfNat idx, nm, ch, off, off)
        off := off + ch.size
      | none => pure ()
  | .obj kvs sz =>
    let mut off := cOff + hdrSize sz
    for kv in kvs do
      out := out.push (textV kv.1.bytes, labelPathName kv.1, kv.2, off + kv.1.size, off)
      off := off + kv.1.size + kv.2.size
  | _ => pure ()
  return out

def eachWalk (fuel : Nat) (tree : Bool) (c : J) (cOff pid : Nat) (pf : ByteArray) (rows : Array (Array Value)) :
    Except String (Array (Array Value)) :=
  match fuel with
  | 0 => .ok rows
  | fuel + 1 => do
    let mut rows := rows
    for (key, nm, ch, chOff, chId) in children c cOff do
      let full := ByteArray.append pf nm
      let v ← toSql ch
      rows := rows.push #[key, v, .text ch.typeName, if ch.isContainer then .null else v, int64OfNat chId,
        if tree then int64OfNat pid else .null, textV full, textV pf]
      if tree && ch.isContainer then
        rows ← eachWalk fuel tree ch chOff chId full rows
    return rows

/-- Where json_tree's first row cuts the root path to get its parent path (jsonEachPathLength). -/
def treePathLen (zr : ByteArray) (doc : J) (rootId : Nat) (n fuel : Nat) : Nat :=
  match fuel with
  | 0 => 1
  | fuel + 1 =>
    if n <= 1 then n else
    let n' := n - 1
    let c := bAt zr n'
    if c == 91 || c == 46 then
      match lookStep (zr.extract 0 n') true fuel0 0 doc 0 0 1 with
      | .ok h => if h.off + h.node.hdr == rootId then n' else treePathLen zr doc rootId n' fuel
      | .error _ => treePathLen zr doc rootId n' fuel
    else treePathLen zr doc rootId n' fuel

/-- json_each / json_tree: the rows (key, value, type, atom, id, parent, fullkey, path) for json and an optional root path. -/
def eachRows (tree : Bool) (json : Value) (root : Option Value) : Except String (Array (Array Value)) := do
  let some doc ← docArg json | return #[]
  let (zr, hit) : ByteArray × Except LErr Hit ←
    match root with
    | none => pure (bs "$", .ok { node := doc })
    | some rv =>
      if rv.isNull then return #[]
      let zr := pathOf rv
      if bAt zr 0 != 36 then throw (badPath rv.toText .pathError)
      pure (zr, lookStep zr true fuel0 0 doc 0 0 1)
  match hit with
  | .error .notFound => return #[]
  | .error _ => throw (badPath (Num.bytesToString zr) .pathError)
  | .ok h =>
    let rootId := if h.lab > 0 then h.lab else h.off
    let v ← toSql h.node
    let mut rows : Array (Array Value) := #[]
    if tree then
      let n := if zr.size == 1 then 1 else treePathLen zr doc rootId zr.size (zr.size + 2)
      let key : Value :=
        if zr.size == 1 || n >= zr.size then .null
        else if bAt zr n == 91 then .int (Num.atoi64Bytes (zr.extract (n + 1) (zr.size - 1))).value
        else if bAt zr (n + 1) == 34 then textV (zr.extract (n + 2) (zr.size - 1))
        else textV (zr.extract (n + 1) zr.size)
      rows := rows.push #[key, v, .text h.node.typeName, if h.node.isContainer then .null else v,
        int64OfNat rootId, .null, textV zr, textV (zr.extract 0 n)]
      if h.node.isContainer then rows ← eachWalk fuel0 true h.node h.off rootId zr rows
    else if h.node.isContainer then
      rows ← eachWalk fuel0 false h.node h.off rootId zr rows
    else
      rows := rows.push #[.null, v, .text h.node.typeName, v, int64OfNat rootId, .null, textV zr, textV zr]
    return rows

end LSql.Json

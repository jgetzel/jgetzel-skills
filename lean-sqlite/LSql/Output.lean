import LSql.Num
import LSql.Record
import LSql.Value

/-! The sqlite3 shell's result output modes, ported from the shell's QRF library (ext/qrf/qrf.c) and
the .mode / .headers / .nullvalue / .separator / .width dot-commands of shell.c.in (sqlite 3.54), for
batch (non-interactive) output: no screen width, no limits, as the shell prints into a pipe.

Every function is total: scans are structural recursion on a fuel bounded by the input size. -/

namespace LSql.Output

open LSql LSql.Num

/-! ### Settings -/

/-- An output mode (the argument of .mode). Besides the modes of the API, c, tcl, jatom, jobject, qbox,
count and off are supported. insert carries the table name. -/
inductive Mode where
  | list | csv | column | box | table | markdown | json | line | quote
  | insert (table : String) | tabs | html | ascii
  | c | tcl | jatom | jobject | qbox | count | off
  deriving Repr, BEq, Inhabited

/-- How text (and column names) are encoded: QRF_TEXT_xxx. -/
inductive TextEnc where
  | auto | plain | sql | csv | html | tcl | json | relaxed
  deriving DecidableEq, Repr, Inhabited

/-- How BLOBs are shown: QRF_BLOB_xxx. -/
inductive BlobEnc where
  | auto | text | sql | hex | tcl | json | size
  deriving DecidableEq, Repr, Inhabited

/-- Control character escaping: QRF_ESC_xxx. -/
inductive Esc where
  | auto | off | ascii | symbol
  deriving DecidableEq, Repr, Inhabited

/-- Whether column names are shown (.headers off|on|always); auto is the mode's own default. -/
inductive Titles where
  | auto | off | on | always
  deriving DecidableEq, Repr, Inhabited

/-- Outer border of box and table. -/
inductive Border where
  | auto | off | on
  deriving DecidableEq, Repr, Inhabited

/-- Settings the shell holds: mode, .headers, .nullvalue, .separator (column and row), .width (per column,
0 = auto), and the other options of .mode. -/
structure Settings where
  mode : Mode := .list
  titles : Titles := .off
  /-- True once .headers was used: a mode change then keeps titles. -/
  hdrSet : Bool := false
  eTitle : TextEnc := .plain
  eText : TextEnc := .plain
  eBlob : BlobEnc := .auto
  eEsc : Esc := .auto
  border : Border := .auto
  nullStr : String := ""
  colSep : String := "|"
  rowSep : String := "\n"
  tableName : String := ""
  /-- Column widths (.width): 0 is automatic, negative is right-aligned. -/
  widths : Array Int := #[]
  /-- Column alignment: 1 left, 2 center, 3 right, 0 unspecified. -/
  aligns : Array UInt8 := #[]
  /-- Word wrap in columns: none is automatic (on). -/
  wordWrap : Option Bool := none
  wrap : Int := 0
  charLimit : Nat := 0
  lineLimit : Nat := 0
  titleLimit : Nat := 0
  multiInsert : Nat := 0
  screenWidth : Nat := 0
  rowCount : Bool := false
  deriving Repr, Inhabited

/-- The drawing style behind a mode (QRF_STYLE_xxx). -/
inductive Style where
  | box | column | count | csv | html | insert | json | jobject | line | list | markdown | off | table
  deriving DecidableEq, Repr

def Mode.style : Mode → Style
  | .csv => .csv
  | .list | .quote | .tabs | .ascii | .c | .tcl | .jatom => .list
  | .column => .column
  | .box | .qbox => .box
  | .table => .table
  | .markdown => .markdown
  | .json => .json
  | .jobject => .jobject
  | .line => .line
  | .insert _ => .insert
  | .html => .html
  | .count => .count
  | .off => .off

/-- aModeInfo of shell.c: separators and null text the mode sets (none: left as they are), text and title
encodings, blob encoding and default header setting. -/
structure ModeInfo where
  cSep : Option String
  rSep : Option String
  nullS : Option String
  text : TextEnc
  hdrEnc : TextEnc
  blob : BlobEnc
  hdr : Titles

def Mode.info : Mode → ModeInfo
  | .ascii => ⟨some "\x1f", some "\x1e", some "", .plain, .plain, .auto, .off⟩
  | .box => ⟨none, none, some "", .plain, .plain, .auto, .always⟩
  | .c => ⟨some ",", some "\n", some "NULL", .tcl, .tcl, .tcl, .off⟩
  | .column => ⟨none, none, some "", .plain, .plain, .auto, .always⟩
  | .count => ⟨none, none, none, .auto, .auto, .auto, .auto⟩
  | .csv => ⟨some ",", some "\r\n", some "", .csv, .csv, .auto, .off⟩
  | .html => ⟨none, none, some "null", .html, .html, .auto, .always⟩
  | .insert _ => ⟨none, none, some "NULL", .sql, .sql, .auto, .off⟩
  | .jatom => ⟨some ",", some "\n", some "null", .json, .json, .auto, .off⟩
  | .jobject => ⟨none, some "\n", some "null", .json, .json, .auto, .auto⟩
  | .json => ⟨none, none, some "null", .json, .json, .auto, .auto⟩
  | .line => ⟨some ": ", some "\n", some "", .plain, .plain, .auto, .auto⟩
  | .list => ⟨some "|", some "\n", some "", .plain, .plain, .auto, .off⟩
  | .markdown => ⟨none, none, some "", .plain, .plain, .auto, .always⟩
  | .off => ⟨none, none, none, .auto, .auto, .auto, .auto⟩
  | .qbox => ⟨none, none, some "NULL", .sql, .plain, .auto, .always⟩
  | .quote => ⟨some ",", some "\n", some "NULL", .sql, .sql, .auto, .off⟩
  | .table => ⟨none, none, some "", .plain, .plain, .auto, .always⟩
  | .tabs => ⟨some "\t", some "\n", some "", .csv, .csv, .auto, .off⟩
  | .tcl => ⟨some " ", some "\n", some "\"\"", .tcl, .tcl, .tcl, .off⟩

/-- modeChange of shell.c: switch the mode, resetting what the mode sets. -/
def Settings.changeMode (s : Settings) (m : Mode) : Settings :=
  let mi := m.info
  { s with
    mode := m
    colSep := mi.cSep.getD s.colSep
    rowSep := mi.rSep.getD s.rowSep
    nullStr := mi.nullS.getD s.nullStr
    eText := mi.text
    eBlob := mi.blob
    titles := if s.hdrSet then s.titles else mi.hdr
    eTitle := mi.hdrEnc
    border := .auto
    rowCount := false }

/-- .headers off|on|always. -/
def Settings.setHeaders (s : Settings) (t : Titles) : Settings :=
  { s with titles := t, hdrSet := true, eTitle := s.mode.info.hdrEnc }

/-- .nullvalue STRING. -/
def Settings.setNullValue (s : Settings) (z : String) : Settings := { s with nullStr := z }

/-- .separator COL ?ROW?. -/
def Settings.setSeparator (s : Settings) (col : String) (row : Option String := none) : Settings :=
  { s with colSep := col, rowSep := row.getD s.rowSep }

/-- .width N1 N2 ... (already converted to integers). -/
def Settings.setWidths (s : Settings) (ws : List Int) : Settings :=
  { s with widths := (ws.map fun w => max (-10000) (min 10000 w)).toArray }

/-! ### Text helpers -/

/-- The byte at i, or 0 past the end. -/
@[inline] private def ba (b : ByteArray) (i : Nat) : UInt8 := byteAt b i

@[inline] private def isAlpha (c : UInt8) : Bool := (65 ≤ c && c ≤ 90) || (97 ≤ c && c ≤ 122) || c == 95
@[inline] private def isAlnum (c : UInt8) : Bool := isAlpha c || isDigit c

private def spaces (n : Nat) : ByteArray := bytesRepeat 32 n

private def padSp (b : ByteArray) (n : Nat) : ByteArray :=
  if n == 0 then b else b ++ bytesRepeat 32 n

private def strBytes (s : String) : ByteArray := cstr (textBytes s)

private def hexLo : UInt8 → UInt8
  | n => if n < 10 then 48 + n else 87 + n

/-- Drop trailing spaces (qrfRTrim). -/
private def rtrimSp (b : ByteArray) : ByteArray :=
  go b.size b.size
where
  go (j : Nat) : Nat → ByteArray
    | 0 => b.extract 0 j
    | f + 1 => if j > 0 && ba b (j - 1) == 32 then go (j - 1) f else if j == b.size then b else b.extract 0 j

/-! ### Unicode width (sqlite3_qrf_wcwidth and friends) -/

private def uwFirst : Array UInt32 := #[0x300, 0x370, 0x483, 0x487, 0x488, 0x48a, 0x591, 0x5be, 0x5bf, 0x5c0, 0x5c1, 0x5c3, 0x5c4, 0x5c6, 0x5c7, 0x5c8, 0x600, 0x604, 0x610, 0x616, 0x64b, 0x65f, 0x670, 0x671, 0x6d6, 0x6e5, 0x6e7, 0x6e9, 0x6ea, 0x6ee, 0x70f, 0x710, 0x711, 0x712, 0x730, 0x74b, 0x7a6, 0x7b1, 0x7eb, 0x7f4, 0x901, 0x903, 0x93c, 0x93d, 0x941, 0x949, 0x94d, 0x94e, 0x951, 0x955, 0x962, 0x964, 0x981, 0x982, 0x9bc, 0x9bd, 0x9c1, 0x9c5, 0x9cd, 0x9ce, 0x9e2, 0x9e4, 0xa01, 0xa03, 0xa3c, 0xa3d, 0xa41, 0xa43, 0xa47, 0xa49, 0xa4b, 0xa4e, 0xa70, 0xa72, 0xa81, 0xa83, 0xabc, 0xabd, 0xac1, 0xac6, 0xac7, 0xac9, 0xacd, 0xace, 0xae2, 0xae4, 0xb01, 0xb02, 0xb3c, 0xb3d, 0xb3f, 0xb40, 0xb41, 0xb44, 0xb4d, 0xb4e, 0xb56, 0xb57, 0xb82, 0xb83, 0xbc0, 0xbc1, 0xbcd, 0xbce, 0xc3e, 0xc41, 0xc46, 0xc49, 0xc4a, 0xc4e, 0xc55, 0xc57, 0xcbc, 0xcbd, 0xcbf, 0xcc0, 0xcc6, 0xcc7, 0xccc, 0xcce, 0xce2, 0xce4, 0xd41, 0xd44, 0xd4d, 0xd4e, 0xdca, 0xdcb, 0xdd2, 0xdd5, 0xdd6, 0xdd7, 0xe31, 0xe32, 0xe34, 0xe3b, 0xe47, 0xe4f, 0xeb1, 0xeb2, 0xeb4, 0xeba, 0xebb, 0xebd, 0xec8, 0xece, 0xf18, 0xf1a, 0xf35, 0xf36, 0xf37, 0xf38, 0xf39, 0xf3a, 0xf71, 0xf7f, 0xf80, 0xf85, 0xf86, 0xf88, 0xf90, 0xf98, 0xf99, 0xfbd, 0xfc6, 0xfc7, 0x102d, 0x1031, 0x1032, 0x1033, 0x1036, 0x103b, 0x1058, 0x105a, 0x1100, 0x1160, 0x1200, 0x135f, 0x1360, 0x1712, 0x1715, 0x1732, 0x1735, 0x1752, 0x1754, 0x1772, 0x1774, 0x17b4, 0x17b6, 0x17b7, 0x17be, 0x17c6, 0x17c7, 0x17c9, 0x17d4, 0x17dd, 0x17de, 0x180b, 0x180e, 0x18a9, 0x18aa, 0x1920, 0x1923, 0x1927, 0x1929, 0x1932, 0x1933, 0x1939, 0x193c, 0x1a17, 0x1a19, 0x1b00, 0x1b04, 0x1b34, 0x1b35, 0x1b36, 0x1b3b, 0x1b3c, 0x1b3d, 0x1b42, 0x1b43, 0x1b6b, 0x1b74, 0x1dc0, 0x1dcb, 0x1dfe, 0x1e00, 0x200b, 0x2010, 0x202a, 0x202f, 0x2060, 0x2064, 0x206a, 0x2070, 0x20d0, 0x20f0, 0x2329, 0x232b, 0x2e80, 0x302a, 0x3030, 0x303f, 0x3040, 0x3099, 0x309b, 0xa4d0, 0xa806, 0xa807, 0xa80b, 0xa80c, 0xa825, 0xa827, 0xac00, 0xd7a4, 0xf900, 0xfb00, 0xfb1e, 0xfb1f, 0xfe00, 0xfe10, 0xfe1a, 0xfe20, 0xfe24, 0xfe30, 0xfe70, 0xfeff, 0xff00, 0xff61, 0xffe0, 0xffe7, 0xfff9, 0xfffc, 0x10a01, 0x10a04, 0x10a05, 0x10a07, 0x10a0c, 0x10a10, 0x10a38, 0x10a3b, 0x10a3f, 0x10a40, 0x1d167, 0x1d16a, 0x1d173, 0x1d183, 0x1d185, 0x1d18c, 0x1d1aa, 0x1d1ae, 0x1d242, 0x1d245, 0x20000, 0x2fffe, 0x30000, 0x3fffe, 0xe0001, 0xe0002, 0xe0020, 0xe0080, 0xe0100, 0xe01f0]
private def uwW : Array UInt8 := #[0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 2, 1, 2, 0, 2, 1, 2, 0, 2, 1, 0, 1, 0, 1, 0, 1, 2, 1, 2, 1, 0, 1, 0, 2, 1, 0, 1, 2, 1, 0, 2, 1, 2, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 2, 1, 2, 1, 0, 1, 0, 1, 0, 1]

/-- Columns used by code point c (sqlite3_qrf_wcwidth): 0, 1 or 2. -/
def wcwidth (c : Nat) : Nat :=
  if c < 0x300 then 1 else go 0 (uwFirst.size - 1) 24
where
  wAt (i : Nat) : Nat := (uwW.getD i 1).toNat
  fAt (i : Nat) : Nat := (uwFirst.getD i 0).toNat
  fin (iFirst iLast : Nat) : Nat := if fAt iLast > c then wAt iFirst else wAt iLast
  go (iFirst iLast : Nat) : Nat → Nat
    | 0 => fin iFirst iLast
    | fuel + 1 =>
      if iFirst + 1 < iLast then
        let iMid := (iFirst + iLast) / 2
        let cMid := fAt iMid
        if cMid < c then go iMid iLast fuel
        else if cMid > c then go iFirst (iMid - 1) fuel
        else wAt iMid
      else fin iFirst iLast

/-- Length and code point of the multi-byte UTF-8 character at z[i] (sqlite3_qrf_decode_utf8); an invalid
lead gives (1, 0). -/
def decodeUtf8 (z : ByteArray) (i : Nat) : Nat × Nat :=
  let b0 := ba z i
  let b1 := ba z (i + 1)
  let b2 := ba z (i + 2)
  let b3 := ba z (i + 3)
  if b0 &&& 0xe0 == 0xc0 && b1 &&& 0xc0 == 0x80 then
    (2, ((b0 &&& 0x1f).toNat <<< 6) ||| (b1 &&& 0x3f).toNat)
  else if b0 &&& 0xf0 == 0xe0 && b1 &&& 0xc0 == 0x80 && b2 &&& 0xc0 == 0x80 then
    (3, ((b0 &&& 0x0f).toNat <<< 12) ||| ((b1 &&& 0x3f).toNat <<< 6) ||| (b2 &&& 0x3f).toNat)
  else if b0 &&& 0xf8 == 0xf0 && b1 &&& 0xc0 == 0x80 && b2 &&& 0xc0 == 0x80 && b3 &&& 0xc0 == 0x80 then
    (4, ((b0 &&& 0x0f).toNat <<< 18) ||| ((b1 &&& 0x3f).toNat <<< 12) ||| ((b2 &&& 0x3f).toNat <<< 6)
      ||| (b3 &&& 0x3f).toNat)
  else (1, 0)

private def skipRange (z : ByteArray) (lo hi : UInt8) (j : Nat) : Nat → Nat
  | 0 => j
  | f + 1 => let c := ba z j; if lo ≤ c && c ≤ hi then skipRange z lo hi (j + 1) f else j

/-- Length of the VT100 escape sequence starting at the ESC byte z[i], or 0 (qrfIsVt100). -/
def isVt100 (z : ByteArray) (i : Nat) : Nat :=
  if ba z (i + 1) != 91 then 0
  else
    let j := skipRange z 0x30 0x3f (i + 2) (z.size + 1)
    let j := skipRange z 0x20 0x2f j (z.size + 1)
    let c := ba z j
    if c < 0x40 || c > 0x7e then 0 else j - i + 1

/-- Display width of z[o, o+nByte) and its number of line breaks (qrfDisplayWidth): the width of the widest
line, tabs to multiples of 8, other control characters no column (the sqlite3 3.54 binary; the source
counts them as one). -/
def displayWidth (z : ByteArray) (o nByte : Nat) : Nat × Nat :=
  go o 0 0 0 (nByte + 1)
where
  go (i n mx nNL : Nat) : Nat → Nat × Nat
    | 0 => (max mx n, nNL)
    | f + 1 =>
      if i ≥ o + nByte then (max mx n, nNL)
      else
        let c := ba z i
        if c < 32 then
          let k := if c == 27 then isVt100 z i else 0
          if k > 0 then go (i + k) n mx nNL f
          else if c == 9 then go (i + 1) ((n + 8) / 8 * 8) mx nNL f
          else if c == 10 || c == 13 then go (i + 1) 0 (max mx n) (nNL + 1) f
          else go (i + 1) n mx nNL f
        else if c < 128 then go (i + 1) (n + 1) mx nNL f
        else
          let (len, u) := decodeUtf8 z i
          go (i + len) (n + wcwidth u) mx nNL f

/-- Width of a C string: control characters and VT100 escapes count 0 (sqlite3_qrf_wcswidth). -/
def wcswidth (z : ByteArray) : Nat := go 0 0 (z.size + 1)
where
  go (i n : Nat) : Nat → Nat
    | 0 => n
    | f + 1 =>
      let c := ba z i
      if c == 0 then n
      else if c < 32 then
        let k := if c == 27 then isVt100 z i else 0
        if k > 0 then go (i + k) n f else go (i + 1) n f
      else if c < 128 then go (i + 1) (n + 1) f
      else
        let (len, u) := decodeUtf8 z i
        go (i + len) (n + wcwidth u) f

/-- True if the C string z contains a character wider than one column (qrfHasWideChar). -/
private def hasWideChar (z : ByteArray) : Bool := go 0 (z.size + 1)
where
  go (i : Nat) : Nat → Bool
    | 0 => false
    | f + 1 =>
      let c := ba z i
      if c == 0 then false
      else if c ≥ 0xc0 then
        let (len, u) := decodeUtf8 z i
        if wcwidth u > 1 then true else go (i + len) f
      else go (i + 1) f

/-- Shorten a column title to n display columns, with "..." (qrfTitleLimit); tabs and line breaks become
spaces. Returns the title and its width. -/
def titleLimit (z : ByteArray) (N : Nat) : ByteArray × Nat :=
  let (buf, n, ell) := go 0 0 none ByteArray.empty (z.size + 1)
  match ell with
  | some (ei, nE) => if N ≥ 3 then (buf.extract 0 ei ++ "...".toUTF8, nE + 3) else (buf, n)
  | none => (buf, n)
where
  go (i n : Nat) (ell : Option (Nat × Nat)) (buf : ByteArray) : Nat → ByteArray × Nat × Option (Nat × Nat)
    | 0 => (buf, n, ell)
    | f + 1 =>
      let c := ba z i
      if c < 32 then
        if c == 0 then (buf, n, none)
        else
          let k := if c == 27 then isVt100 z i else 0
          if k > 0 then go (i + k) n ell (buf ++ z.extract i (i + k)) f
          else if c == 9 || c == 10 || c == 13 then go (i + 1) n ell (buf.push 32) f
          else go (i + 1) n ell (buf.push c) f
      else if c < 128 then
        let ell' := if ell.isNone && (n : Int) ≥ (N : Int) - 3 then some (i, n) else ell
        if n == N then (buf, n, ell')
        else go (i + 1) (n + 1) ell' (buf.push c) f
      else
        let (len, u) := decodeUtf8 z i
        let w := wcwidth u
        let ell' := if ell.isNone && (n + w : Int) > (N : Int) - 3 then some (i, n) else ell
        if n + w > N then (buf, n, ell')
        else go (i + len) (n + w) ell' (buf ++ z.extract i (i + len)) f

/-- One display line of text: how many bytes of z (from o) go on the current line, how wide they are, and
where the next line starts (qrfWrapLine). w is the column width, bWrap word-wraps. -/
def wrapLine (z : ByteArray) (o w : Nat) (bWrap : Bool) : Nat × Nat × Nat :=
  if ba z o == 0 then (0, 0, 0)
  else
    let (i, n, c) := scan 0 0 0 (z.size + 2)
    if c == 0 then (i, n, i)
    else if c == 10 then (i, n, i + 1)
    else
      let zi := ba z (o + i)
      let (i, n) :=
        if bWrap && zi != 0 && !isSpace zi && isAlnum c == isAlnum zi then
          let half := i / 2
          let k1 := back1 (i : Int) half (i + 1)
          let k :=
            if k1 < half && half > 0 then back2 (i : Int) half (i + 1) else k1
          if k ≥ half then (k.toNat, (displayWidth z o k.toNat).1) else (i, n)
        else (i, n)
      (i, n, skipWs i (z.size + 1))
where
  scan (i n : Nat) (c : UInt8) : Nat → Nat × Nat × UInt8
    | 0 => (i, n, c)
    | f + 1 =>
      if n > w then (i, n, c)
      else
        let c := ba z (o + i)
        if c ≥ 0xc0 then
          let (len, u) := decodeUtf8 z (o + i)
          let wcw := wcwidth u
          if wcw + n > w then (i, n, c) else scan (i + len) (n + wcw) c f
        else if c ≥ 32 then
          if n == w then (i, n, c) else scan (i + 1) (n + 1) c f
        else if c == 0 || c == 10 then (i, n, c)
        else if c == 13 && ba z (o + i + 1) == 10 then (i + 1, n, 10)
        else if c == 9 then
          let wcw := 8 - (n &&& 7)
          if n + wcw > w then (i, n, c) else scan (i + 1) (n + wcw) c f
        else
          let k := if c == 27 then isVt100 z (o + i) else 0
          if k > 0 then scan (i + k) n c f
          else if n == w then (i, n, c)
          else scan (i + 1) (n + 1) c f
  -- k from i-1 down while k >= half: the first space
  back1 (i : Int) (half : Nat) : Nat → Int
    | 0 => (-1)
    | f + 1 => go1 (i - 1) half f
  go1 (k : Int) (half : Nat) : Nat → Int
    | 0 => k
    | f + 1 => if k < (half : Int) then k else if isSpace (ba z (o + k.toNat)) then k else go1 (k - 1) half f
  back2 (i : Int) (half : Nat) : Nat → Int
    | 0 => (-1)
    | f + 1 => go2 i half f
  go2 (k : Int) (half : Nat) : Nat → Int
    | 0 => k
    | f + 1 =>
      if k < (half : Int) then k
      else if isAlnum (ba z (o + (k - 1).toNat)) != isAlnum (ba z (o + k.toNat)) && (ba z (o + k.toNat)) &&& 0xc0 != 0x80 then k
      else go2 (k - 1) half f
  skipWs (i : Nat) : Nat → Nat
    | 0 => i
    | f + 1 =>
      let c := ba z (o + i)
      if c == 32 || c == 9 || c == 13 then skipWs (i + 1) f else i

/-! ### Encoding of values -/

/-- A resolved output specification (qrfInitialize and the shell's shell_exec): what encodings apply and
the texts in use. -/
structure Spec where
  style : Style
  eText : TextEnc
  eTitle : TextEnc
  eBlob : BlobEnc
  eEsc : Esc
  titles : Titles
  nullS : ByteArray
  colSep : ByteArray
  rowSep : ByteArray
  tableName : ByteArray
  /-- zFpFmt is "%0.16g" (json and insert). -/
  fp17 : Bool
  wordWrap : Bool
  border : Bool
  widths : Array Int
  aligns : Array UInt8
  wrap : Int
  charLimit : Nat
  lineLimit : Nat
  titleLimit : Nat
  multiInsert : Nat
  screenWidth : Nat
  rowCount : Bool

/-- The settings the shell would hand to QRF for a statement. -/
def resolve (s : Settings) : Spec :=
  let style := s.mode.style
  let blob0 :=
    if s.eBlob == .auto then
      match s.eText with
      | .relaxed | .sql => BlobEnc.sql
      | .json => .json
      | _ => .text
    else s.eBlob
  let eText1 :=
    match style with
    | .json | .jobject => TextEnc.json
    | .html => .html
    | .insert => .sql
    | .csv => .csv
    | _ => s.eText
  let nullS :=
    match style with
    | .json | .jobject | .html => "null"
    | .insert => "NULL"
    | .csv => ""
    | _ => s.nullStr
  let eEsc :=
    if s.eEsc == .auto then (if style == .csv then Esc.off else .ascii) else s.eEsc
  let eText := if eText1 == .auto then TextEnc.plain else eText1
  let eTitle :=
    if s.eTitle == .auto then
      (match style with | .box | .column | .table => TextEnc.plain | _ => eText)
    else s.eTitle
  let eBlob :=
    if blob0 == .auto then
      match eText with
      | .sql => BlobEnc.sql
      | .csv | .tcl => .tcl
      | .json => .json
      | _ => .text
    else blob0
  let titles :=
    if s.titles == .auto then
      (match style with | .box | .column | .table | .markdown => Titles.on | _ => .off)
    else s.titles
  let tn := match s.mode with | .insert t => t | _ => s.tableName
  { style, eText, eTitle, eBlob, eEsc, titles
    nullS := strBytes nullS
    colSep := strBytes (if style == .csv then "," else s.colSep)
    rowSep := strBytes (if style == .csv then "\r\n" else s.rowSep)
    tableName := strBytes (if tn.isEmpty then "tab" else tn)
    fp17 := style == .json || style == .jobject || style == .insert
    wordWrap := s.wordWrap.getD true
    border := s.border != .off
    widths := s.widths, aligns := s.aligns, wrap := s.wrap
    charLimit := s.charLimit, lineLimit := s.lineLimit, titleLimit := s.titleLimit
    multiInsert := s.multiInsert, screenWidth := s.screenWidth, rowCount := s.rowCount }

/-- Show control characters other than tab, newline and CRLF as ^X or as control pictures (qrfEscape). -/
def escapeCtrl (symbol : Bool) (b : ByteArray) : ByteArray :=
  if !needs 0 (b.size + 1) then b
  else Id.run do
    let mut out := ByteArray.empty
    for i in [0:b.size] do
      let c := ba b i
      if isCtl b i c then
        if symbol then out := ((out.push 0xe2).push 0x90).push (c + 0x80)
        else out := (out.push 94).push (c + 0x40)
      else out := out.push c
    return out
where
  isCtl (b : ByteArray) (i : Nat) (c : UInt8) : Bool :=
    c ≤ 0x1f && c != 9 && c != 10 && (c != 13 || ba b (i + 1) != 10)
  needs (i : Nat) : Nat → Bool
    | 0 => false
    | f + 1 => if i ≥ b.size then false else if isCtl b i (ba b i) then true else needs (i + 1) f

/-- True if some byte of b satisfies p. -/
private def bAny (b : ByteArray) (p : UInt8 → Bool) : Bool := go 0 (b.size + 1)
where
  go (i : Nat) : Nat → Bool
    | 0 => false
    | f + 1 => if i ≥ b.size then false else if p (ba b i) then true else go (i + 1) f

/-- The digit character for 0..9 (a byte). -/
private def d8 (n : UInt8) : UInt8 := n + 48

/-- True if the text can be shown unquoted in the relaxed quoting style (qrfRelaxable). -/
def relaxable (nullS : ByteArray) (z : ByteArray) : Bool :=
  let z0 := ba z 0
  if z0 == 39 || isSpace z0 then false
  else if z0 == 0 then nullS.size != 0
  else
    let n := z.size
    if ba z (n - 1) == 39 || isSpace (ba z (n - 1)) then false
    else if nullS == z then false
    else
      let i := if z0 == 45 || z0 == 43 then 1 else 0
      if z.extract i z.size == "Inf".toUTF8 then false
      else if ba z i == 48 && (ba z (i + 1) == 120 || ba z (i + 1) == 88) then
        let i := i + 2
        let j := skipRange' z i (fun c => isDigit c || (97 ≤ c && c ≤ 102) || (65 ≤ c && c ≤ 70)) (z.size + 1)
        j == i || ba z j != 0
      else
        let i? : Option Nat :=
          if ba z i == 46 && isDigit (ba z (i + 1)) then some (i + 1)
          else if !isDigit (ba z i) then none
          else
            let j := skipRange' z i isDigit (z.size + 1)
            some (if ba z j == 46 then j + 1 else j)
        match i? with
        | none => true
        | some i =>
          let i := skipRange' z i isDigit (z.size + 1)
          if ba z i == 0 then false
          else if ba z i == 101 || ba z i == 69 then
            let i := i + 1
            let i := if ba z i == 43 || ba z i == 45 then i + 1 else i
            if !isDigit (ba z i) then true
            else
              let i := skipRange' z (i + 1) isDigit (z.size + 1)
              ba z i != 0
          else true
where
  skipRange' (z : ByteArray) (j : Nat) (p : UInt8 → Bool) : Nat → Nat
    | 0 => j
    | f + 1 => if p (ba z j) then skipRange' z (j + 1) p f else j

/-- True if the C string z contains the C string sub (strstr; the empty string is always found). -/
private def containsSub (z sub : ByteArray) : Bool :=
  if sub.size == 0 then true else go 0 (z.size + 1)
where
  go (i : Nat) : Nat → Bool
    | 0 => false
    | f + 1 =>
      if i + sub.size > z.size then false
      else if z.extract i (i + sub.size) == sub then true else go (i + 1) f

private def pushStr (out : ByteArray) (s : String) : ByteArray := out ++ s.toUTF8

/-- Text as an SQL literal: printf's %Q, or %#Q (unistr for control characters) when escaping is on. -/
private def sqlQuote (alt : Bool) (z : ByteArray) : ByteArray := Id.run do
  let ctl := alt && bAny z (fun c => c ≤ 0x1f)
  let mut out := if ctl then "unistr('".toUTF8 else ByteArray.empty.push 39
  for c in z do
    if c == 39 then out := (out.push 39).push 39
    else if ctl && c == 92 then out := (out.push 92).push 92
    else if ctl && c ≤ 0x1f then
      out := ((((out.push 92).push 117).push 48).push 48).push (if c ≥ 0x10 then 49 else 48) |>.push (hexUp (c &&& 15))
    else out := out.push c
  out := out.push 39
  if ctl then out := out.push 41
  return out
where
  hexUp (n : UInt8) : UInt8 := if n < 10 then 48 + n else 87 + n

private def quoteDq (z : ByteArray) : ByteArray := Id.run do
  let mut out := ByteArray.empty.push 34
  for c in z do
    if c == 34 then out := (out.push 34).push 34 else out := out.push c
  return out.push 34

/-- qrfEncodeText: encode the C string z for the text encoding of sp and escape control characters. -/
def encodeText (sp : Spec) (z : ByteArray) : ByteArray :=
  let r : ByteArray :=
    match sp.eText with
    | .relaxed => if relaxable sp.nullS z then z else sqlQuote (sp.eEsc != .off) z
    | .sql => sqlQuote (sp.eEsc != .off) z
    | .csv =>
      if z.size == 0 || bAny z (fun c => c < 0x21 || c == 0x22 || c == 0x27 || c ≥ 0x7f) || containsSub z sp.colSep
      then quoteDq z else z
    | .html => Id.run do
      let mut out := ByteArray.empty
      for c in z do
        if c == 62 then out := pushStr out "&gt;"
        else if c == 38 then out := pushStr out "&amp;"
        else if c == 60 then out := pushStr out "&lt;"
        else if c == 34 then out := pushStr out "&quot;"
        else if c == 39 then out := pushStr out "&#39;"
        else out := out.push c
      return out
    | .tcl | .json => Id.run do
      let json := sp.eText == .json
      let mut out := ByteArray.empty.push 34
      for c in z do
        if c ≥ 0x20 && c != 92 && c != 34 then out := out.push c
        else if c == 34 then out := pushStr out "\\\""
        else if c == 92 then out := pushStr out "\\\\"
        else if c == 8 then out := pushStr out "\\b"
        else if c == 12 then out := pushStr out "\\f"
        else if c == 10 then out := pushStr out "\\n"
        else if c == 13 then out := pushStr out "\\r"
        else if c == 9 then out := pushStr out "\\t"
        else if json then
          out := ((((out.push 92).push 117).push 48).push 48).push (hexLo (c >>> 4)) |>.push (hexLo (c &&& 15))
        else out := (((out.push 92).push (d8 (c >>> 6))).push (d8 ((c >>> 3) &&& 7))).push (d8 (c &&& 7))
      return out.push 34
    | _ => z
  if sp.eEsc == .off || sp.eEsc == .auto then r else escapeCtrl (sp.eEsc == .symbol) r

/-- Digits of an unsigned number (printf %d for a Nat). -/
private def natBytes (n : Nat) : ByteArray := (toString n).toUTF8

/-- A REAL as the shell prints it: the text of the value, or "%0.16g" for json and insert. -/
private def realBytes (sp : Spec) (f : Float) : ByteArray :=
  if sp.fp17 then renderFloat f .generic false 16 { zero := true } 0 else fmtRealBytes f

private def blobHex (b : ByteArray) (pre post : String) : ByteArray := Id.run do
  let mut out := pre.toUTF8
  for c in b do out := (out.push (hexLo (c >>> 4))).push (hexLo (c &&& 15))
  return pushStr out post

private def blobBytes (sp : Spec) (b : ByteArray) : ByteArray :=
  match sp.eBlob with
  | .hex => blobHex b "" ""
  | .sql => blobHex b "x'" "'"
  | .tcl => Id.run do
    let mut out := ByteArray.empty.push 34
    for c in b do
      out := (((out.push 92).push (d8 ((c >>> 6) &&& 3))).push (d8 ((c >>> 3) &&& 7))).push (d8 (c &&& 7))
    return out.push 34
  | .json => Id.run do
    let mut out := ByteArray.empty.push 34
    for c in b do
      out := (((((out.push 92).push 117).push 48).push 48).push (hexLo (c >>> 4))).push (hexLo (c &&& 15))
    return out.push 34
  | .size => ("(" ++ toString b.size ++ "-byte blob)").toUTF8
  | _ => if sp.eEsc == .off || sp.eEsc == .auto then b else escapeCtrl (sp.eEsc == .symbol) b

/-- Cut a rendered value to the character limit, with "..." (end of qrfRenderValue). -/
private def limitChars (sp : Spec) (r : ByteArray) : ByteArray :=
  if sp.charLimit == 0 || r.size ≤ sp.charLimit then r
  else
    let limit := max sp.charLimit 4
    let (ii, w) := go 0 0 limit (r.size + 1)
    if w > limit then r.extract 0 ii ++ "...".toUTF8 else r
where
  go (ii w limit : Nat) : Nat → Nat × Nat
    | 0 => (ii, w)
    | f + 1 =>
      let c := ba r ii
      if c < 32 then
        let k := if c == 27 then isVt100 r ii else 0
        if k > 0 then go (ii + k) w limit f
        else if ii ≥ r.size then (ii, w)
        else go (ii + 1) w limit f
      else if c < 128 then
        if w + 1 > limit then (ii, w + 1) else go (ii + 1) (w + 1) limit f
      else
        let (len, u) := decodeUtf8 r ii
        let w' := w + wcwidth u
        if w' > limit then (ii, w') else go (ii + len) w' limit f

/-- qrfRenderValue: one value as the shell prints it. -/
def renderValue (sp : Spec) (v : Value) : ByteArray :=
  let r : ByteArray :=
    match v with
    | .int i => int64ToBytes i
    | .real f => realBytes sp f
    | .blob b => blobBytes sp b
    | .null => if sp.style == .html then encodeText sp sp.nullS else sp.nullS
    | .text s => encodeText sp (strBytes s)
  match v with
  | .blob _ =>
    -- text blobs of the row by row styles are flushed before the limit is applied
    if sp.eBlob == .text && sp.style != .box && sp.style != .column && sp.style != .table
        && sp.style != .markdown && sp.style != .line then r
    else limitChars sp r
  | _ => limitChars sp r

/-! ### Row by row styles -/

private def isKeyword (z : ByteArray) : Bool :=
  let u := (bytesToString z).toUpper
  keywords.contains u
where
  keywords : Array String := #["ABORT", "ACTION", "ADD", "AFTER", "ALL", "ALTER", "ALWAYS", "ANALYZE", "AND", "AS", "ASC", "ATTACH", "AUTOINCREMENT", "BEFORE", "BEGIN", "BETWEEN", "BY", "CASCADE", "CASE", "CAST", "CHECK", "COLLATE", "COLUMN", "COMMIT", "CONFLICT", "CONSTRAINT", "CREATE", "CROSS", "CURRENT", "CURRENT_DATE", "CURRENT_TIME", "CURRENT_TIMESTAMP", "DATABASE", "DEFAULT", "DEFERRED", "DEFERRABLE", "DELETE", "DESC", "DETACH", "DISTINCT", "DO", "DROP", "END", "EACH", "ELSE", "ESCAPE", "EXCEPT", "EXCLUSIVE", "EXCLUDE", "EXISTS", "EXPLAIN", "FAIL", "FILTER", "FIRST", "FOLLOWING", "FOR", "FOREIGN", "FROM", "FULL", "GENERATED", "GLOB", "GROUP", "GROUPS", "HAVING", "IF", "IGNORE", "IMMEDIATE", "IN", "INDEX", "INDEXED", "INITIALLY", "INNER", "INSERT", "INSTEAD", "INTERSECT", "INTO", "IS", "ISNULL", "JOIN", "KEY", "LAST", "LEFT", "LIKE", "LIMIT", "MATCH", "MATERIALIZED", "NATURAL", "NO", "NOT", "NOTHING", "NOTNULL", "NULL", "NULLS", "OF", "OFFSET", "ON", "OR", "ORDER", "OTHERS", "OUTER", "OVER", "PARTITION", "PLAN", "PRAGMA", "PRECEDING", "PRIMARY", "QUERY", "RAISE", "RANGE", "RECURSIVE", "REFERENCES", "REGEXP", "REINDEX", "RELEASE", "RENAME", "REPLACE", "RESTRICT", "RETURNING", "RIGHT", "ROLLBACK", "ROW", "ROWS", "SAVEPOINT", "SELECT", "SET", "TABLE", "TEMP", "TEMPORARY", "THEN", "TIES", "TO", "TRANSACTION", "TRIGGER", "UNBOUNDED", "UNION", "UNIQUE", "UPDATE", "USING", "VACUUM", "VALUES", "VIEW", "VIRTUAL", "WHEN", "WHERE", "WINDOW", "WITH", "WITHIN", "WITHOUT"]

/-- qrf_need_quote: an identifier needs quoting unless it is a plain non-keyword word. -/
private def needQuote (z : ByteArray) : Bool :=
  z.size == 0 || !isAlpha (ba z 0) || bAny z (fun c => !isAlnum c) || isKeyword z

/-- An identifier as INSERT statements show it: bare, or "..." with " doubled. -/
private def ident (z : ByteArray) : ByteArray :=
  if needQuote z then quoteDq z else z

private def encTitles (sp : Spec) (names : Array ByteArray) (i : Nat) : ByteArray :=
  encodeText { sp with eText := sp.eTitle } (names.getD i ByteArray.empty)

private def showTitles (sp : Spec) : Bool := sp.titles == .on || sp.titles == .always

private def renderList (sp : Spec) (names : Array ByteArray) (rows : Array (Array Value)) : ByteArray := Id.run do
  if rows.isEmpty && !(sp.titles == .always && names.size > 0) then return ByteArray.empty
  let mut out := ByteArray.empty
  if showTitles sp then
    for i in [0:names.size] do
      if i > 0 then out := out ++ sp.colSep
      out := out ++ encTitles sp names i
    out := out ++ sp.rowSep
  for r in rows do
    for i in [0:names.size] do
      if i > 0 then out := out ++ sp.colSep
      out := out ++ renderValue sp (r.getD i .null)
    out := out ++ sp.rowSep
  return out

private def renderJson (sp : Spec) (names : Array ByteArray) (rows : Array (Array Value)) (obj : Bool) : ByteArray := Id.run do
  if rows.isEmpty then return ByteArray.empty
  let mut out := ByteArray.empty
  let mut first := true
  for r in rows do
    if first then out := pushStr out (if obj then "{" else "[{")
    else out := pushStr out (if obj then "}\n{" else "},\n{")
    first := false
    for i in [0:names.size] do
      if i > 0 then out := out.push 44
      out := out ++ encodeText sp (names.getD i ByteArray.empty)
      out := out.push 58
      out := out ++ renderValue sp (r.getD i .null)
  return pushStr out (if obj then "}\n" else "}]\n")

private def renderHtml (sp : Spec) (names : Array ByteArray) (rows : Array (Array Value)) : ByteArray := Id.run do
  if rows.isEmpty && !(sp.titles == .always && names.size > 0) then return ByteArray.empty
  let mut out := ByteArray.empty
  if showTitles sp then
    out := pushStr out "<tr>"
    for i in [0:names.size] do
      out := pushStr out "\n<th>"
      out := out ++ encodeText sp (names.getD i ByteArray.empty)
    out := pushStr out "\n</tr>\n"
  for r in rows do
    out := pushStr out "<tr>"
    for i in [0:names.size] do
      out := pushStr out "\n<td>"
      out := out ++ renderValue sp (r.getD i .null)
    out := pushStr out "\n</tr>\n"
  return out

private def renderInsert (sp : Spec) (names : Array ByteArray) (rows : Array (Array Value)) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  let mut nIns := 0
  let mx := sp.multiInsert
  let tn := ident sp.tableName
  for r in rows do
    let mut buf := ByteArray.empty
    if nIns == 0 || nIns ≥ mx then
      if nIns != 0 then
        buf := pushStr buf ";\n"
        nIns := 0
      buf := pushStr buf "INSERT INTO " ++ tn
      if showTitles sp then
        for i in [0:names.size] do
          buf := (buf.push (if i == 0 then 40 else 44)) ++ ident (names.getD i ByteArray.empty)
        buf := buf.push 41
      buf := pushStr buf " VALUES("
    else buf := pushStr buf ",\n  ("
    for i in [0:names.size] do
      if i > 0 then buf := buf.push 44
      buf := buf ++ renderValue sp (r.getD i .null)
    nIns := nIns + buf.size + 2
    if nIns ≥ mx then
      buf := pushStr buf ");\n"
      nIns := 0
    else buf := buf.push 41
    out := out ++ buf
  if nIns != 0 then out := pushStr out ";\n"
  return out

/-- qrfWidthPrint: the name in w columns, right-justified when w is negative. -/
private def widthPrint (w : Int) (a : ByteArray) : ByteArray :=
  let aw := w.natAbs
  let (i, n) := go 0 0 aw (a.size + 1)
  let body := a.extract 0 i
  if n ≥ aw then body
  else if w < 0 then padSp ByteArray.empty (aw - n) ++ body
  else padSp body (aw - n)
where
  go (i n aw : Nat) : Nat → Nat × Nat
    | 0 => (i, n)
    | f + 1 =>
      let c := ba a i
      if c == 0 then (i, n)
      else if c &&& 0xc0 == 0xc0 then
        let (len, u) := decodeUtf8 a i
        let x := wcwidth u
        if x + n > aw then (i, n) else go (i + len) (n + x) aw f
      else if c == 27 && isVt100 a i > 0 then go (i + isVt100 a i) n aw f
      else if c < 0x20 then go (i + 1) (n + 1) aw f
      else if n ≥ aw then (i, n)
      else go (i + 1) (n + 1) aw f

private def renderLine (sp : Spec) (names : Array ByteArray) (rows : Array (Array Value)) : ByteArray := Id.run do
  if rows.isEmpty then return ByteArray.empty
  let cols : Array ByteArray := names.map fun z => if sp.titleLimit > 0 then (titleLimit z sp.titleLimit).1 else z
  let mxCol := cols.foldl (fun m z => max m (wcswidth z)) 0
  let nSep := sp.colSep.size
  let mxWidth : Int := if sp.screenWidth == 0 then 2147483647 else sp.screenWidth
  let mxW : Nat := (max 2 (mxWidth - (nSep + mxCol : Nat))).toNat
  let mxH : Nat := if sp.lineLimit == 0 then 2147483647 else sp.lineLimit
  let mut out := ByteArray.empty
  let mut nRow := 0
  for r in rows do
    if nRow > 0 then out := out.push 10
    nRow := nRow + 1
    for i in [0:names.size] do
      out := out ++ widthPrint (-(mxCol : Int)) (cols.getD i ByteArray.empty)
      out := out ++ sp.colSep
      let direct : Bool := match r.getD i .null with | .blob _ => decide (sp.eBlob = .text) && decide (sp.eEsc = .off) | _ => false
      let v0 := if direct then ByteArray.empty else renderValue sp (r.getD i .null)
      if direct then
        match r.getD i .null with
        | .blob b => out := out ++ b
        | _ => pure ()
      let mut z := v0
      let mut o := 0
      let mut cnt := 0
      for _ in [0:v0.size + 2] do
        if cnt == 0 || ba z o != 0 then
          let (nThis0, _, iNext0) := wrapLine z o mxW sp.wordWrap
          if cnt > 0 then out := padSp out (mxCol + nSep)
          cnt := cnt + 1
          let mut nThis := nThis0
          let mut iNext := iNext0
          if cnt > mxH then
            z := "...".toUTF8
            o := 0
            nThis := 3
            iNext := 3
          out := (out ++ z.extract o (o + nThis)).push 10
          o := o + iNext
  return out

/-! ### Columnar styles (box, column, table, markdown) -/

private def glyph (n : Nat) (g : String) : ByteArray := Id.run do
  let gb := g.toUTF8
  let mut out := ByteArray.empty
  for _ in [0:n] do out := out ++ gb
  return out

/-- qrfAppendWithTabs: n bytes of text with tabs expanded and control characters as control pictures. -/
private def appendWithTabs (out : ByteArray) (z : ByteArray) (o nVal : Nat) : ByteArray :=
  if !bAny (z.extract o (o + nVal)) (· < 32) then out ++ z.extract o (o + nVal)
  else Id.run do
    let mut out := out
    let mut col := 0
    let mut i := o
    let stop := o + nVal
    for _ in [0:nVal + 1] do
      if i < stop then
        let c := ba z i
        if c < 32 then
          let k := if c == 27 then isVt100 z i else 0
          if k > 0 then
            out := out ++ z.extract i (i + k)
            i := i + k
          else if c == 9 then
            let k := 8 - (col &&& 7)
            out := padSp out k
            col := col + k
            i := i + 1
          else if c == 13 && i + 1 == stop then
            i := i + 1
          else
            col := col + 1
            out := ((out.push 0xe2).push 0x90).push (c + 0x80)
            i := i + 1
        else if c < 128 then
          out := out.push c
          col := col + 1
          i := i + 1
        else
          let (len, u) := decodeUtf8 z i
          out := out ++ z.extract i (min (i + len) (max stop (i + 1)))
          col := col + wcwidth u
          i := i + len
    return out

private def printAligned (out : ByteArray) (z : ByteArray) (o : Nat) (e : UInt8) (bNum : Bool) (nVal nWS : Nat) : ByteArray :=
  let eA0 := e &&& 3
  let eA := if eA0 == 0 && bNum then 3 else eA0
  if eA == 2 then padSp (appendWithTabs (padSp out (nWS / 2)) z o nVal) (nWS - nWS / 2)
  else if eA == 3 then appendWithTabs (padSp out nWS) z o nVal
  else padSp (appendWithTabs out z o nVal) nWS

/-- Default alignment of the table body (qrfLoadAlignment). -/
private def loadAlignment (sp : Spec) (nCol : Nat) : Array UInt8 := Id.run do
  let mut e : Array UInt8 := Array.replicate nCol 0
  for i in [0:nCol] do
    if i < sp.aligns.size then
      let ax := sp.aligns.getD i 0
      if ax &&& 3 != 0 then e := e.setIfInBounds i (ax &&& 3)
    else if i < sp.widths.size then
      if sp.widths.getD i 0 < 0 then e := e.setIfInBounds i 3
  return e

/-- Narrow the widest columns to fit the screen width (qrfRestrictScreenWidth); returns the widths, the
margin and whether some cell may need several lines. -/
private def restrictScreen (sp : Spec) (w : Array Nat) (mxW : Array Nat) (fx : Array Bool) (multi : Bool) :
    Array Nat × Nat × Bool := Id.run do
  let nCol := w.size
  if sp.screenWidth == 0 then return (w, 2, multi)
  let sepW : Nat := if sp.style == .column then nCol * 2 - 2 else (nCol * 3 + 1) - (if sp.border then 0 else 2)
  let sumW0 := w.foldl (· + ·) 0
  if sp.screenWidth ≥ sumW0 + sepW then return (w, 2, multi)
  let sepW2 : Nat := if sp.style == .column then nCol - 1 else (nCol + 1) - (if sp.border then 0 else 2)
  let targetW := (sp.screenWidth : Int) - sepW2
  let mut w := w
  let mut sumW := sumW0
  let mut multi := multi
  for _ in [0:sumW0 + 1] do
    if (sumW : Int) > targetW then
      let mut ix : Option Nat := none
      let mut mx := 0
      for i in [0:nCol] do
        let wi := w.getD i 0
        if !(fx.getD i false) && wi > mx && wi > 8 && (wi > 16 || wi * 2 > mxW.getD i 0) then
          ix := some i
          mx := wi
      match ix with
      | none => pure ()
      | some jx =>
        let gain0 := if mx ≥ 16 then mx / 2 else mx - 8
        let gain : Nat := if (sumW : Int) - gain0 < targetW then (sumW : Int) - targetW |>.toNat else gain0
        sumW := sumW - gain
        w := w.setIfInBounds jx (w.getD jx 0 - gain)
        multi := true
  return (w, 0, multi)

private def rowSeparator (sp : Spec) (w : Array Nat) (nMargin : Nat) (cSep : UInt8) : ByteArray := Id.run do
  let nCol := w.size
  let mut out := ByteArray.empty
  if nCol > 0 then
    if sp.border then out := out.push cSep
    out := padDash out (w.getD 0 0 + nMargin)
    for i in [1:nCol] do
      out := out.push cSep
      out := padDash out (w.getD i 0 + nMargin)
    if sp.border then out := out.push cSep
  return out.push 10
where
  padDash (out : ByteArray) (n : Nat) : ByteArray := out ++ bytesRepeat 45 n

private def boxSeparator (sp : Spec) (w : Array Nat) (nMargin : Nat) (s1 s2 s3 : String) (dbl : Bool) : ByteArray := Id.run do
  let nCol := w.size
  let mut out := ByteArray.empty
  let line := fun (n : Nat) => glyph n (if dbl then "═" else "─")
  if nCol > 0 then
    if sp.border then out := pushStr out s1
    out := out ++ line (w.getD 0 0 + nMargin)
    for i in [1:nCol] do
      out := pushStr out s2
      out := out ++ line (w.getD i 0 + nMargin)
    if sp.border then out := pushStr out s3
  return out.push 10

private def columnSeparator (w : Array Nat) (colSep rowSep : ByteArray) : ByteArray := Id.run do
  let nCol := w.size
  let mut out := ByteArray.empty
  for j in [0:nCol] do
    out := out ++ bytesRepeat 45 (w.getD j 0)
    if j < nCol - 1 then out := out ++ colSep
    else out := rtrimSp out ++ rowSep
  return out

/-- The physical lines of one table row: cells wrapped to their column widths, up to the line limit. -/
private def drawRow (cells : Array ByteArray) (nums : Array Bool) (es : Array UInt8) (ws : Array Nat)
    (rowStart colSep rowSep : ByteArray) (bWW bRTrim : Bool) (mxH : Nat) : ByteArray := Id.run do
  let nCol := cells.size
  let mut out := ByteArray.empty
  let mut offs : Array Nat := Array.replicate nCol 0
  let mut nRow := 0
  let mut bMore := false
  let total := cells.foldl (fun a z => a + z.size) 0
  let mut go := true
  for _ in [0:total + 2] do
    if go then
      let mut line := rowStart
      bMore := false
      for j in [0:nCol] do
        let z := cells.getD j ByteArray.empty
        let o := offs.getD j 0
        let w := ws.getD j 0
        let (nThis, nWide, iNext) := wrapLine z o w bWW
        let nWS := w - nWide
        line := printAligned line z o (es.getD j 0) (nums.getD j false) nThis nWS
        offs := offs.setIfInBounds j (o + iNext)
        if o + iNext < z.size && ba z (o + iNext) != 0 then bMore := true
        if j < nCol - 1 then line := line ++ colSep
        else line := (if bRTrim then rtrimSp line else line) ++ rowSep
      out := out ++ line
      nRow := nRow + 1
      go := bMore && nRow < mxH
  if bMore then
    let mut line := rowStart
    for j in [0:nCol] do
      let z := cells.getD j ByteArray.empty
      let o := offs.getD j 0
      let w := ws.getD j 0
      if o ≥ z.size || ba z o == 0 then line := padSp line w
      else
        let nE := min 3 w
        line := printAligned line "...".toUTF8 0 (es.getD j 0) (nums.getD j false) nE (w - nE)
      if j < nCol - 1 then line := line ++ colSep
      else line := (if bRTrim then rtrimSp line else line) ++ rowSep
    out := out ++ line
  return out

private def renderColumnar (sp : Spec) (names : Array ByteArray) (rows : Array (Array Value)) : ByteArray := Id.run do
  let nCol := names.size
  if nCol == 0 then return ByteArray.empty
  if rows.isEmpty && sp.titles != .always then
    return (if sp.rowCount then "(0 rows)\n".toUTF8 else ByteArray.empty)
  let hasTitle := showTitles sp
  let mut az : Array ByteArray := Array.mkEmpty ((rows.size + 1) * nCol)
  let mut aiWth : Array Nat := Array.mkEmpty ((rows.size + 1) * nCol)
  let mut abNum : Array Bool := Array.mkEmpty ((rows.size + 1) * nCol)
  let mut mxW : Array Nat := Array.replicate nCol 0
  let mut multi := false
  if hasTitle then
    for i in [0:nCol] do
      let z0 := encTitles sp names i
      let (z, w, nNL) :=
        if sp.titleLimit > 0 then (let (z, w) := titleLimit z0 sp.titleLimit; (z, w, 0))
        else (let (w, nNL) := displayWidth z0 0 z0.size; (z0, w, nNL))
      az := az.push z
      aiWth := aiWth.push w
      abNum := abNum.push false
      if w > mxW.getD i 0 then mxW := mxW.setIfInBounds i w
      if nNL > 0 then multi := true
  let mut pre := ByteArray.empty
  for r in rows do
    for i in [0:nCol] do
      let v := r.getD i .null
      let z ←
        match v with
        | .blob b =>
          if sp.eBlob == .text && sp.eEsc == .off then
            pre := pre ++ b
            pure ByteArray.empty
          else pure (renderValue sp v)
        | _ => pure (renderValue sp v)
      let (w, nNL) := displayWidth z 0 z.size
      az := az.push z
      aiWth := aiWth.push w
      abNum := abNum.push (match v with | .int _ | .real _ => true | _ => false)
      if w > mxW.getD i 0 then mxW := mxW.setIfInBounds i w
      if nNL > 0 then multi := true
  -- alignment and widths of every column
  let mut es : Array UInt8 := if hasTitle then Array.replicate nCol 2 else loadAlignment sp nCol
  let mut ws : Array Nat := Array.replicate nCol 0
  let mut fx : Array Bool := Array.replicate nCol false
  for i in [0:nCol] do
    let mut w : Int := 0
    if i < sp.widths.size then
      w := sp.widths.getD i 0
      if w < 0 then
        w := -w
        if sp.aligns.size > i && sp.aligns.getD i 0 &&& 3 == 0 then es := es.setIfInBounds i (es.getD i 0 ||| 3)
      if w != 0 then fx := fx.setIfInBounds i true
    let mxi := mxW.getD i 0
    if w == 0 then
      w := mxi
      if sp.wrap > 0 && w > sp.wrap then
        w := sp.wrap
        multi := true
        if w == 1 then
          for j in [0:rows.size + (if hasTitle then 1 else 0)] do
            if w == 1 && hasWideChar (az.getD (j * nCol + i) ByteArray.empty) then w := 2
    else if (!multi || w == 1) && (mxi : Int) > w then
      multi := true
      if w == 1 then w := 2
    ws := ws.setIfInBounds i w.toNat
  let (wsF, nMargin, multiF) := restrictScreen sp ws mxW fx multi
  -- the table frame
  let rowStart0 : String := match sp.style with
    | .box => if nMargin != 0 then "│ " else "│"
    | .column => ""
    | _ => if nMargin != 0 then "| " else "|"
  let colSep : ByteArray := match sp.style with
    | .box => (if nMargin != 0 then " │ " else "│").toUTF8
    | .column => if nMargin < 2 then " ".toUTF8 else spaces (min nMargin 5)
    | _ => (if nMargin != 0 then " | " else "|").toUTF8
  let rowSep0 : String := match sp.style with
    | .box => if nMargin != 0 then " │\n" else "│\n"
    | .column => "\n"
    | _ => if nMargin != 0 then " |\n" else "|\n"
  let noBorder := !sp.border && (sp.style == .box || sp.style == .table)
  let rowStart : ByteArray :=
    if noBorder then (if sp.style == .box then rowStart0.toUTF8.extract 3 rowStart0.utf8ByteSize else rowStart0.toUTF8.extract 1 rowStart0.utf8ByteSize)
    else rowStart0.toUTF8
  let rowSep : ByteArray := if noBorder then "\n".toUTF8 else rowSep0.toUTF8
  let mut out := pre
  if sp.style == .box && sp.border then out := out ++ boxSeparator sp wsF nMargin "╭" "┬" "╮" false
  if sp.style == .table && sp.border then out := out ++ rowSeparator sp wsF nMargin 43
  let bWW := sp.wordWrap && multiF
  let bRTrim := sp.style == .column || noBorder
  let mxH : Nat := if sp.lineLimit == 0 then 2147483647 else sp.lineLimit
  let nTotal := rows.size + (if hasTitle then 1 else 0)
  for r in [0:nTotal] do
    let cells := az.extract (r * nCol) (r * nCol + nCol)
    let nums := abNum.extract (r * nCol) (r * nCol + nCol)
    out := out ++ drawRow cells nums es wsF rowStart colSep rowSep bWW bRTrim mxH
    if (r == 0 || multiF) && r + 1 < nTotal then
      let isTitleSep := r == 0 && hasTitle
      if isTitleSep then es := loadAlignment sp nCol
      match sp.style with
      | .table => if isTitleSep || multiF then out := out ++ rowSeparator sp wsF nMargin 43
      | .box =>
        if isTitleSep then out := out ++ boxSeparator sp wsF nMargin "╞" "╪" "╡" true
        else if multiF then out := out ++ boxSeparator sp wsF nMargin "├" "┼" "┤" false
      | .markdown => if isTitleSep then out := out ++ rowSeparator sp wsF nMargin 124
      | .column =>
        if isTitleSep then out := out ++ columnSeparator wsF colSep rowSep
        else if multiF then out := (rtrimSp out).push 10
      | _ => pure ()
  -- the bottom
  if sp.border || rows.isEmpty then
    match sp.style with
    | .box =>
      if !rows.isEmpty then out := out ++ boxSeparator sp wsF nMargin "╰" "┴" "╯" false
      else out := out ++ boxSeparator sp wsF nMargin "╘" "╧" "╛" true
    | .table => out := out ++ rowSeparator sp wsF nMargin 43
    | .markdown => if rows.isEmpty then out := out ++ rowSeparator sp wsF nMargin 124
    | .column => if rows.isEmpty then out := out ++ columnSeparator wsF colSep rowSep
    | _ => pure ()
  if sp.rowCount then
    out := pushStr out ("(" ++ toString rows.size ++ " row" ++ (if rows.size == 1 then "" else "s") ++ ")\n")
  return out

/-- The row count line shown after the rows by .mode --rowcount on (the columnar styles add their own). -/
private def rowCountLine (sp : Spec) (n : Nat) : ByteArray :=
  let rows := toString n ++ (if n == 1 then " row" else " rows")
  match sp.style with
  | .list | .csv => ("(" ++ rows ++ ")\n").toUTF8
  | .line => ((if n > 0 then "\n" else "") ++ "(" ++ rows ++ ")\n").toUTF8
  | .insert => ("/* " ++ rows ++ " inserted */\n").toUTF8
  | .html => ("<!-- " ++ rows ++ " -->\n").toUTF8
  | _ => ByteArray.empty

/-- One statement's result in the current mode: the bytes the shell prints (names: column names; rows of
values). A statement with no result columns prints nothing; with columns but no rows, the table modes print
their header and frame (when headers are on, as box, column, table, markdown and html have by default),
count prints the row count and the other modes print nothing. -/
def render (s : Settings) (names : Array String) (rows : Array (Array Value)) : ByteArray :=
  let sp := resolve s
  let ns := names.map strBytes
  let count := fun (b : ByteArray) =>
    if sp.rowCount && ns.size > 0 then b ++ rowCountLine sp rows.size else b
  match sp.style with
  | .list | .csv => count (renderList sp ns rows)
  | .json => renderJson sp ns rows false
  | .jobject => renderJson sp ns rows true
  | .html => count (renderHtml sp ns rows)
  | .insert => count (renderInsert sp ns rows)
  | .line => count (renderLine sp ns rows)
  | .count => (toString rows.size ++ "\n").toUTF8
  | .off => ByteArray.empty
  | .box | .column | .table | .markdown => renderColumnar sp ns rows


/-! ### The .mode command -/

private def digitVal (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - 48)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 87)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 55)
  else none

private def digitsOf (base : Nat) : List Char → Nat → Nat × List Char
  | c :: r, acc =>
    match digitVal c with
    | some d => if d < base then digitsOf base r (acc * base + d) else (acc, c :: r)
    | none => (acc, c :: r)
  | [], acc => (acc, [])

/-- sqlite3's integerValue: decimal or 0x hex with an optional K, M, G, KB, MB, GB, KiB, MiB, GiB suffix;
saturating at the Int64 range. -/
def integerValue (z : String) : Int :=
  let cs := z.toList
  let (neg, cs) := match cs with | '-' :: r => (true, r) | '+' :: r => (false, r) | r => (false, r)
  let (v, rest) :=
    match cs with
    | '0' :: 'x' :: r => digitsOf 16 r 0
    | r => digitsOf 10 r 0
  let mult : Nat :=
    match (String.ofList rest).toLower with
    | "kib" => 1024 | "mib" => 1048576 | "gib" => 1073741824
    | "kb" | "k" => 1000 | "mb" | "m" => 1000000 | "gb" | "g" => 1000000000
    | _ => 1
  let big : Nat := 9223372036854775807
  let v := v * mult
  if neg then (if v > big then -(big : Int) - 1 else -(v : Int)) else (if v > big then (big : Int) else (v : Int))

/-- sqlite3's booleanValue: a number, on/yes, off/no; anything else is false. -/
def booleanValue (z : String) : Bool :=
  let l := z.toLower
  if l == "on" || l == "yes" then true
  else if l == "off" || l == "no" then false
  else if !z.isEmpty && z.all Char.isDigit then decide (integerValue z % 4294967296 != 0)
  else if z.startsWith "0x" && z.length > 2 && (z.drop 2).all (fun c => (digitVal c).isSome) then
    decide (integerValue z % 4294967296 != 0)
  else false

private def modeFind : String → Option Mode
  | "ascii" => some .ascii | "box" => some .box | "c" => some .c | "column" => some .column
  | "count" => some .count | "csv" => some .csv | "html" => some .html | "insert" => some (.insert "")
  | "jatom" => some .jatom | "jobject" => some .jobject | "json" => some .json | "line" => some .line
  | "list" => some .list | "markdown" => some .markdown | "off" => some .off | "qbox" => some .qbox
  | "quote" => some .quote | "table" => some .table | "tabs" => some .tabs | "tcl" => some .tcl
  | _ => none

/-- pickStr: the index of z in the list. -/
private def pick (z : String) (names : List String) : Option Nat := names.findIdx? (· == z)

/-- The message pickStr builds when z is none of the names. -/
private def pickMsg (names : List String) : String := Id.run do
  let n := names.length
  let mut s := "should be"
  let mut i := 0
  for z in names do
    if i + 1 == n then s := s ++ ", or" else if i > 0 then s := s ++ ","
    s := s ++ " " ++ z
    i := i + 1
  return s

/-- The text dotCmdError prints for argument iArg of the .mode command (a: ".mode" and its arguments); every
line is to be printed after the shell's location prefix ("line N:") and one space. -/
private def dotErr (a : Array String) (iArg : Nat) (brief : String) (detail : Option String) : String := Id.run do
  let mut lines : Array String := #[]
  if iArg < a.size then
    let orig := String.intercalate " " a.toList
    let mut ofst := 0
    for k in [0:iArg] do ofst := ofst + (a.getD k "").utf8ByteSize + 1
    let nPrompt := brief.utf8ByteSize + 5
    lines := lines.push orig
    if ofst > nPrompt then lines := lines.push ("".pushn ' ' (1 + ofst - nPrompt) ++ brief ++ " ---^")
    else lines := lines.push ("".pushn ' ' ofst ++ "^--- " ++ brief)
  match detail with
  | some d => lines := lines.push d
  | none => pure ()
  return String.intercalate "\n" lines.toList

private def clamp16 (x : Int) : Nat := (max 0 (min 32767 x)).toNat
private def clamp32 (x : Int) : Nat := (max 0 (min 2147483647 x)).toNat

/-- A decimal prefix of z (sscanf %d), after leading blanks. -/
private def leadingInt (z : String) : Option Int :=
  let cs := z.toList.dropWhile Char.isWhitespace
  let (neg, cs) := match cs with | '-' :: r => (true, r) | '+' :: r => (false, r) | r => (false, r)
  match cs with
  | c :: _ => if c.isDigit then (let (v, _) := digitsOf 10 cs 0; some (if neg then -(v : Int) else v)) else none
  | [] => none

/-- modeSetLimit: on, off, or L,C[,T]. -/
private def setLimit (s : Settings) (z : String) : Option Settings :=
  if z == "on" then some { s with lineLimit := 5, charLimit := 300, titleLimit := 20 }
  else if z == "off" then some { s with lineLimit := 0, charLimit := 0, titleLimit := 0 }
  else
    let parts := z.splitOn ","
    match parts.map leadingInt with
    | some l :: some c :: rest =>
      let t := match rest with | some t :: _ => some t | _ => none
      if l < 0 || c < 0 || (match t with | some t => decide (t < 0) | none => false) then none
      else
        some { s with lineLimit := clamp16 l, charLimit := clamp32 c
                      titleLimit := match t with | some t => clamp16 t | none => s.titleLimit }
    | _ => none

/-- The --widths list: comma-separated integers. -/
private def parseWidths (z : String) : Except (String × String) (Array Int) := Id.run do
  let mut cs := z.toList.dropWhile Char.isWhitespace
  let mut out : Array Int := #[]
  for _ in [0:z.length + 1] do
    if !cs.isEmpty then
      let neg := match cs with | '-' :: d :: _ => d.isDigit | _ => false
      let body := if neg then cs.drop 1 else cs
      let digits := body.takeWhile Char.isDigit
      if digits.isEmpty then return .error ("syntax error", "should be a comma-separated list if integers")
      let (w, _) := digitsOf 10 digits 0
      if w > 10000 then return .error ("width too big", "Maximum column width is 10000")
      out := out.push (if cs.head? == some '-' then -(w : Int) else w)
      let rest := body.drop digits.length
      let rest := match rest with | ',' :: r => r | r => r
      cs := rest.dropWhile Char.isWhitespace
  return .ok out

/-- Parses the arguments of a .mode command (e.g. ["csv"], ["insert", "t"], ["box"]) into the new settings
(.mode also resets the separators for csv, tabs, list, ... as modeChange does). An unknown mode or option is
an error: the text sqlite3 prints for it, each line to be printed after the shell's "line N:" prefix and a
space ("unknown mode", with the argument pointed at, and a hint). Supported options: --align, --blob-quote,
--border, --charlimit, --linelimit, --titlelimit, --multiinsert, --tablename, --rowsep, --colsep, --null,
--escape, --limits, --quote, --noquote, --reset, --rowcount, --screenwidth, --titles, --widths, --wrap,
--ww, --wordwrap, --textjsonb (ignored), -v (ignored). Not supported: --ifmt, --fpfmt, --once, --tag, --list
and the modes tty, psql, split and www. -/
def setMode (s0 : Settings) (args : List String) : Except String Settings := do
  let a : Array String := #[".mode"] ++ args.toArray
  let nArg := a.size
  let argAt := fun (k : Nat) => a.getD k ""
  let mut s := s0
  let mut iMode : Int := -1
  let mut i := 1
  for _ in [0:nArg + 1] do
    if i < nArg then
      let z0 := argAt i
      let z := if z0.startsWith "--" then String.ofList (z0.toList.drop 1) else z0
      let opt := if z.startsWith "-" then String.ofList (z.toList.drop 1) else ""
      let missing := fun (k : Nat) => throw (dotErr a k "missing argument" none)
      if !z.startsWith "-" && iMode < 0 && (modeFind z0).isSome then
        iMode := i
        s := s.changeMode ((modeFind z0).getD .list)
        if i + 1 < nArg && !(argAt (i + 1)).startsWith "-" then
          i := i + 1
          s := { s with tableName := argAt i }
      else if z0 == "batch" && iMode < 0 then
        iMode := i
        s := ({ (default : Settings) with hdrSet := s.hdrSet }).changeMode .list
      else if !z.startsWith "-" then
        throw (dotErr a i (if iMode > 0 then "bad argument" else "unknown mode") (some "Use \".help .mode\" for more info"))
      else
        match opt with
        | "align" =>
          if i + 1 ≥ nArg then missing i
          i := i + 1
          let mut al : Array UInt8 := #[]
          let mut nErr := 0
          for c in (argAt i).toList do
            if c == 'l' || c == 'L' then al := al.push 1
            else if c == 'c' || c == 'C' then al := al.push 2
            else if c == 'r' || c == 'R' then al := al.push 3
            else
              al := al.push 0
              nErr := nErr + 1
          s := { s with aligns := al }
          if nErr > 0 then
            throw (dotErr a i "bad alignment string" (some "Should contain only characters L, C, and R."))
        | "blob" | "blob-quote" =>
          if i + 1 ≥ nArg then missing i
          i := i + 1
          match pick (argAt i) ["auto", "text", "sql", "hex", "tcl", "json", "size"] with
          | some k => s := { s with eBlob := [BlobEnc.auto, .text, .sql, .hex, .tcl, .json, .size].getD k .auto }
          | none => pure ()
        | "border" =>
          if i + 1 ≥ nArg then missing i
          i := i + 1
          match pick (argAt i) ["auto", "off", "on"] with
          | some k => s := { s with border := [Border.auto, .off, .on].getD k .auto }
          | none => pure ()
        | "charlimit" | "linelimit" | "titlelimit" | "multiinsert" =>
          if i + 1 ≥ nArg then missing i
          i := i + 1
          let w := integerValue (argAt i)
          if opt == "charlimit" then s := { s with charLimit := clamp32 w }
          else if opt == "linelimit" then s := { s with lineLimit := clamp16 w }
          else if opt == "titlelimit" then s := { s with titleLimit := clamp16 w }
          else s := { s with multiInsert := clamp32 w }
        | "tablename" | "rowsep" | "colsep" | "null" =>
          if i + 1 ≥ nArg then missing i
          i := i + 1
          let v := argAt i
          if opt == "tablename" then s := { s with tableName := v }
          else if opt == "rowsep" then s := { s with rowSep := v }
          else if opt == "colsep" then s := { s with colSep := v }
          else s := { s with nullStr := v }
        | "escape" =>
          if i + 1 ≥ nArg then missing i
          i := i + 1
          match pick (argAt i) ["auto", "off", "ascii", "symbol"] with
          | some k => s := { s with eEsc := [Esc.auto, .off, .ascii, .symbol].getD k .auto }
          | none => throw (dotErr a i "unknown escape type" (some (pickMsg ["auto", "off", "ascii", "symbol"])))
        | "limits" =>
          if i + 1 ≥ nArg then missing i
          i := i + 1
          match setLimit s (argAt i) with
          | some s' => s := s'
          | none =>
            throw (dotErr a i "bad argument" (some ("Should be \"on\" or \"off\" or \"L,C,T\" where L, C, and T are unsigned integers")))
        | "noquote" => s := { s with eText := .plain, eBlob := .auto }
        | "quote" =>
          let names := ["off", "on", "sql", "csv", "html", "tcl", "json", "relaxed", "no", "yes", "0", "1", ""]
          let zq := if i + 1 < nArg then some (argAt (i + 1)) else none
          let k : Option Nat := match zq with | some q => pick q names | none => none
          let k : Nat ←
            match k with
            | some k =>
              i := i + 1
              pure (if k ≥ 8 then k &&& 1 else k)
            | none =>
              match zq with
              | some q =>
                if !q.startsWith "-" && (iMode > 0 || (modeFind q).isNone) then
                  throw (dotErr a (i + 1) "unknown" (some (pickMsg ["off", "on", "sql", "csv", "html", "tcl", "json", "relaxed"])))
                else pure 1
              | none => pure 1
          if k == 1 then s := { s with nullStr := "NULL" }
          s := { s with eText := [TextEnc.plain, .sql, .sql, .csv, .html, .tcl, .json, .relaxed].getD k .plain }
        | "reset" =>
          s := (default : Settings).changeMode s.mode
        | "rowcount" =>
          if i + 1 ≥ nArg then missing i
          i := i + 1
          s := { s with rowCount := booleanValue (argAt i) }
        | "screenwidth" | "sw" =>
          if i + 1 ≥ nArg then missing i
          i := i + 1
          let v := argAt i
          if v == "off" || v == "auto" then s := { s with screenWidth := 0 }
          else s := { s with screenWidth := (max 0 (min 10000 (integerValue v))).toNat }
        | "titles" | "title" =>
          if i + 1 ≥ nArg then missing i
          i := i + 1
          let names := ["off", "on", "always", "auto", "plain", "sql", "csv", "html", "tcl", "json"]
          match pick (argAt i) names with
          | none => throw (dotErr a i "bad --titles value" (some (pickMsg names)))
          | some k =>
            s := { s with hdrSet := false }
            if k ≤ 2 then s := { s with titles := [Titles.off, .on, .always].getD k .off }
            else if k == 3 then s := { s with eTitle := s.mode.info.hdrEnc, titles := s.mode.info.hdr }
            else
              s := { s with eTitle := [TextEnc.plain, .sql, .csv, .html, .tcl, .json].getD (k - 4) .plain }
              if s.titles == .off then s := { s with titles := .always }
        | "widths" | "width" =>
          if i + 1 ≥ nArg then missing i
          i := i + 1
          match parseWidths (argAt i) with
          | .ok ws => s := { s with widths := ws }
          | .error (brief, detail) => throw (dotErr a (i + 1) brief (some detail))
        | "wrap" =>
          if i + 1 ≥ nArg then missing i
          i := i + 1
          s := { s with wrap := max (-10000) (min 10000 (integerValue (argAt i))) }
        | "ww" => s := { s with wordWrap := some true }
        | "wordwrap" =>
          if i + 1 ≥ nArg then missing i
          i := i + 1
          s := { s with wordWrap := some (booleanValue (argAt i)) }
        | "textjsonb" =>
          if i + 1 ≥ nArg then missing i
          i := i + 1
        | "v" | "verbose" => pure ()
        | "ifmt" | "fpfmt" | "once" | "tag" | "list" =>
          throw (dotErr a i "unsupported" (some "this option is not supported by lean-sqlite"))
        | _ => throw (dotErr a i "bad option" (some ("Use \".help .mode\" for more info")))
      i := i + 1
  -- the table name of insert mode
  match s.mode with
  | .insert _ => s := { s with mode := .insert s.tableName }
  | _ => pure ()
  return s

end LSql.Output

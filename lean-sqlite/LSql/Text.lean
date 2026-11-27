import LSql.Bytes
/-! Text values as bytes: sqlite's TEXT is bytes, a Lean `String` is valid UTF-8. -/
namespace LSql

/-- Byte `i` of a string's UTF-8 (0 past its end). -/
@[inline] def strByte (s : String) (i : Nat) : UInt8 :=
  if h : (⟨i⟩ : String.Pos.Raw) < s.rawEndPos then s.getUTF8Byte ⟨i⟩ h else 0

/-! ## Text that is not valid UTF-8

sqlite's TEXT is bytes; a Lean `String` is valid UTF-8. A text value's bytes and its `String` correspond one to one: a byte that is
not part of a valid UTF-8 scalar is the private-use char U+10FF00 + byte (an *escaped byte*, bytes 0x80..0xFF), and the 128 chars
U+10FF80..U+10FFFF are themselves read as four escaped bytes. `textOfBytes` and `textBytes` are inverse; a string is canonical when it is
`textOfBytes` of its bytes (a valid scalar is a char, never escaped bytes), which text joined from pieces restores with `canonText`. -/

/-- The char standing for the raw byte `b` (0x80..0xFF). -/
def escChar (b : UInt8) : Char := Char.ofNat (0x10FF00 + b.toNat)

/-- Whether a char stands for a raw byte. -/
def isEscChar (c : Char) : Bool := 0x10FF80 ≤ c.val

/-- The raw byte an escaped byte stands for. -/
def escByte (c : Char) : UInt8 := (c.val - 0x10FF00).toUInt8

/-- Whether a string holds an escaped byte: its UTF-8 holds F4 8F BE or F4 8F BF. -/
def hasEsc (s : String) : Bool := s.length != s.utf8ByteSize && go 0 s.utf8ByteSize
where
  go (i : Nat) : Nat → Bool
    | 0 => false
    | f+1 => (strByte s i == 0xF4 && strByte s (i+1) == 0x8F && strByte s (i+2) ≥ 0xBE) || go (i+1) f

/-- A text value's bytes: its UTF-8, an escaped byte as the raw byte. -/
def textBytes (s : String) : ByteArray :=
  if hasEsc s then
    s.foldl (fun acc c => if isEscChar c then acc.push (escByte c) else acc ++ (String.singleton c).toUTF8) ByteArray.empty
  else s.toUTF8

/-- The length of a text value's bytes. -/
def textLen (s : String) : Nat := if hasEsc s then (textBytes s).size else s.utf8ByteSize

/-- The valid UTF-8 scalar starting at byte `i` of `b` (other than one standing for a raw byte) and its length. -/
def scalarAt (b : ByteArray) (i : Nat) : Option (Char × Nat) :=
  let c := rd b i
  let n := if c < 0x80 then 1 else if 0xC2 ≤ c && c ≤ 0xDF then 2 else if 0xE0 ≤ c && c ≤ 0xEF then 3
    else if 0xF0 ≤ c && c ≤ 0xF4 then 4 else 0
  if n == 0 || i + n > b.size then none
  else if n == 1 then some (Char.ofNat c.toNat, 1)
  else match (String.fromUTF8? (b.extract i (i + n))).map String.toList with
    | some [ch] => if isEscChar ch then none else some (ch, n)
    | _ => none

/-- A text value's bytes as a string, byte by byte: each valid scalar a char, each other byte an escaped byte. -/
def lenientText (b : ByteArray) : String := go "" 0 b.size
where
  go (acc : String) (i : Nat) : Nat → String
    | 0 => acc
    | f+1 =>
      if i ≥ b.size then acc else
      match scalarAt b i with
      | some (ch, n) => go (acc.push ch) (i + n) f
      | none => go (acc.push (escChar (rd b i))) (i + 1) f

/-- A text value's bytes as a String (bytes that are not valid UTF-8, which sqlite keeps, as escaped bytes). -/
def textOfBytes (b : ByteArray) : String :=
  match String.fromUTF8? b with
  | some s => if s.length != b.size && (b.findIdx? (· == 0xF4)).isSome then lenientText b else s
  | none => lenientText b

/-- The string of the same bytes with valid scalars as chars again: joining strings of escaped bytes can complete a scalar (a lead
byte, then its continuation bytes). -/
def canonText (s : String) : String := if hasEsc s then textOfBytes (textBytes s) else s

end LSql

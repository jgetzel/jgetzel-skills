import LSql.Bytes
import LSql.Text
import LSql.Value
/-! sqlite's record format (fileformat2.html §2.1): a varint header size, one serial type per column, then the bodies. -/
namespace LSql

/-- Serial type and body length of a value. -/
def serialType : Value → UInt64 × Nat
  | .null => (0, 0)
  | .int i =>
    if i == 0 then (8, 0) else if i == 1 then (9, 0)
    else if -128 ≤ i && i ≤ 127 then (1, 1)
    else if -32768 ≤ i && i ≤ 32767 then (2, 2)
    else if -8388608 ≤ i && i ≤ 8388607 then (3, 3)
    else if -2147483648 ≤ i && i ≤ 2147483647 then (4, 4)
    else if -140737488355328 ≤ i && i ≤ 140737488355327 then (5, 6)
    else (6, 8)
  | .real _ => (7, 8)
  | .text s => let n := textLen s; (13 + 2 * n.toUInt64, n)
  | .blob b => (12 + 2 * b.size.toUInt64, b.size)

/-- Body length of a serial type. -/
def serialLen (t : UInt64) : Nat :=
  match t with
  | 0 | 8 | 9 | 10 | 11 => 0
  | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 8 | 7 => 8
  | t => ((t - 12) / 2).toNat

/-- Appends a value's body. -/
def pushBody (b : ByteArray) : Value → ByteArray
  | .null => b
  | v@(.int i) => let (_, n) := serialType v; pushBE b i.toUInt64 n
  | .real f => pushBE b f.toBits 8
  | .text s => b ++ textBytes s
  | .blob x => b ++ x

/-- A record's header for fields of these serial types and body lengths (with room for the bodies). -/
def recordHeader (types : Array (UInt64 × Nat)) : ByteArray :=
  let h : Nat := types.foldl (fun n (t, _) => n + varintLen t) 0
  -- the header size counts its own varint
  let hs := if h + 1 < 128 then h + 1 else if h + 2 < 16384 then h + 2 else h + 3
  let bodyLen : Nat := types.foldl (fun n (_, l) => n + l) 0
  let b := ByteArray.emptyWithCapacity (hs + bodyLen)
  let b := putVarint b hs.toUInt64
  types.foldl (fun b (t, _) => putVarint b t) b

/-- The record of a row. -/
def encodeRecord (vals : Array Value) : ByteArray :=
  vals.foldl pushBody (recordHeader (vals.map serialType))

/-- The integer of an integer serial type (1 to 6, 8, 9) whose body starts at `o`: read in place, no `Value`. -/
def intField (p : ByteArray) (o : Nat) (t : UInt64) : Int64 :=
  match t with
  | 8 => 0
  | 9 => 1
  | t =>
    let n := serialLen t
    let s := (64 - 8 * n).toUInt64
    ((rdBE p o n) <<< s).toInt64 >>> s.toInt64

/-- The real of serial type 7 whose body starts at `o`. -/
def realField (p : ByteArray) (o : Nat) : Float := Float.ofBits (rdBE p o 8)

/-- The value of serial type `t` whose body starts at `o`. -/
def decodeField (p : ByteArray) (o : Nat) (t : UInt64) : Value :=
  match t with
  | 0 => .null
  | 8 => .int 0
  | 9 => .int 1
  | 7 => .real (realField p o)
  | 10 | 11 => .null
  | t =>
    if t ≤ 6 then .int (intField p o t)
    else
      let n := serialLen t
      let bytes := p.extract o (o + n)
      if t % 2 == 0 then .blob bytes else .text (textOfBytes bytes)

/-- The serial types of a record and each body's offset. -/
def recordFields (p : ByteArray) : Array (UInt64 × Nat) :=
  let (hs, k) := getVarint p 0
  go hs.toNat k hs.toNat #[] (p.size + 1)
where
  go (hs : Nat) (pos body : Nat) (acc : Array (UInt64 × Nat)) : Nat → Array (UInt64 × Nat)
    | 0 => acc
    | fuel+1 =>
      if pos ≥ hs then acc else
      let (t, k) := getVarint p pos
      go hs (pos + k) (body + serialLen t) (acc.push (t, body)) fuel

/-- All columns of a record. -/
def decodeRecord (p : ByteArray) : Array Value :=
  (recordFields p).map fun (t, o) => decodeField p o t

/-- Column `i` of a record (NULL past its last column, as for a column added by ALTER TABLE). -/
def recordColumn (p : ByteArray) (i : Nat) : Value :=
  let (hs, k) := getVarint p 0
  go hs.toNat k hs.toNat i (p.size + 1)
where
  go (hs : Nat) (pos body : Nat) (i : Nat) : Nat → Value
    | 0 => .null
    | fuel+1 =>
      if pos ≥ hs then .null else
      let (t, k) := getVarint p pos
      if i == 0 then decodeField p body t else go hs (pos + k) (body + serialLen t) (i - 1) fuel

/-- The number of columns in a record. -/
def recordArity (p : ByteArray) : Nat := (recordFields p).size

/-- A record of `n` fields: field `i` copied from record `old` (`fields`: its `recordFields`) where `keep i`, serial type
and body bytes, nothing decoded; else the value `v i`. -/
def spliceRecord (old : ByteArray) (fields : Array (UInt64 × Nat)) (n : Nat) (keep : Nat → Bool) (v : Nat → Value) :
    ByteArray :=
  let kept (i : Nat) : Bool := i < fields.size && keep i
  let types := Array.ofFn (n := n) fun j =>
    let i := j.val
    if kept i then let t := (fields.getD i (0, 0)).1; (t, serialLen t) else serialType (v i)
  n.fold (fun i _ b =>
    if kept i then old.copySlice (fields.getD i (0, 0)).2 b b.size (types.getD i (0, 0)).2 false else pushBody b (v i))
    (recordHeader types)

end LSql

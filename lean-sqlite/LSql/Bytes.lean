/-! Total byte access, big-endian integers and sqlite's varints (fileformat2.html §1.6). -/
namespace LSql

/-- A byte of `a`, 0 past the end (a corrupt file reads zeros rather than failing). -/
@[inline] def rd (a : ByteArray) (i : Nat) : UInt8 :=
  if h : i < a.size then a[i] else 0

@[inline] def rd16 (a : ByteArray) (i : Nat) : Nat :=
  (rd a i).toNat <<< 8 ||| (rd a (i+1)).toNat

@[inline] def rd32 (a : ByteArray) (i : Nat) : UInt32 :=
  (rd a i).toUInt32 <<< 24 ||| (rd a (i+1)).toUInt32 <<< 16 ||| (rd a (i+2)).toUInt32 <<< 8 ||| (rd a (i+3)).toUInt32

/-- A big-endian unsigned integer of `n` bytes (n ≤ 8) at `i`. -/
def rdBE (a : ByteArray) (i : Nat) : (n : Nat) → UInt64
  | 0 => 0
  | n+1 => (rdBE a i n) <<< 8 ||| (rd a (i+n)).toUInt64

@[inline] def push16 (b : ByteArray) (v : Nat) : ByteArray :=
  (b.push (v >>> 8).toUInt8).push v.toUInt8

@[inline] def push32 (b : ByteArray) (v : UInt32) : ByteArray :=
  (((b.push (v >>> 24).toUInt8).push (v >>> 16).toUInt8).push (v >>> 8).toUInt8).push v.toUInt8

/-- The low `n` bytes of `v`, big-endian. -/
def pushBE (b : ByteArray) (v : UInt64) : (n : Nat) → ByteArray
  | 0 => b
  | n+1 => (b.push (v >>> (8 * n).toUInt64).toUInt8) |> fun b' => pushBE' b' v n
where
  pushBE' (b : ByteArray) (v : UInt64) : Nat → ByteArray
    | 0 => b
    | n+1 => pushBE' (b.push (v >>> (8 * n).toUInt64).toUInt8) v n

/-- `n` zero bytes appended. -/
def pushZeros (b : ByteArray) : Nat → ByteArray
  | 0 => b
  | n+1 => pushZeros (b.push 0) n

/-- A 2-byte big-endian value written at `i` (no change past the end). -/
def set16 (a : ByteArray) (i : Nat) (v : Nat) : ByteArray :=
  let a := if h : i < a.size then a.set i (v >>> 8).toUInt8 else a
  if h : i + 1 < a.size then a.set (i+1) v.toUInt8 else a

def set32 (a : ByteArray) (i : Nat) (v : UInt32) : ByteArray :=
  let a := set16 a i (v >>> 16).toNat
  set16 a (i+2) (v &&& 0xFFFF).toNat

/-! ## Varints: 1 to 9 bytes, 7 bits per byte big-endian with the high bit as "more", the 9th byte all 8 bits. -/

/-- The varint at `i` and its length in bytes. -/
def getVarint (a : ByteArray) (i : Nat) : UInt64 × Nat :=
  go 0 0 9
where
  /-- `k` bytes read so far, `fuel` bytes left (the 9th byte is the one read with fuel 1, all 8 bits) -/
  go (acc : UInt64) (k : Nat) : (fuel : Nat) → UInt64 × Nat
    | 0 => (acc, k)
    | 1 => ((acc <<< 8) ||| (rd a (i+k)).toUInt64, k+1)
    | f+2 =>
      let c := rd a (i+k)
      let acc := (acc <<< 7) ||| (c &&& 0x7f).toUInt64
      if c < 0x80 then (acc, k+1) else go acc (k+1) (f+1)

/-- Bytes the varint of `v` takes. -/
def varintLen (v : UInt64) : Nat :=
  if v < 0x80 then 1 else if v < 0x4000 then 2 else if v < 0x200000 then 3 else if v < 0x10000000 then 4
  else if v < 0x800000000 then 5 else if v < 0x40000000000 then 6 else if v < 0x2000000000000 then 7
  else if v < 0x100000000000000 then 8 else 9

/-- Appends the varint of `v`. -/
def putVarint (b : ByteArray) (v : UInt64) : ByteArray :=
  if v < 0x80 then b.push v.toUInt8 else
  if v >>> 56 != 0 then
    -- 9 bytes: 8 bytes of 7 bits (the high 56 bits of v), then the low 8 bits whole
    let hi := v >>> 8
    let b := groups b hi 8 true
    b.push v.toUInt8
  else
    let n := varintLen v
    groups b v n false
where
  /-- the `n` 7-bit groups of `v`, the high bit set on all but the last (on all when `more`) -/
  groups (b : ByteArray) (v : UInt64) (n : Nat) (more : Bool) : ByteArray :=
    n.fold (fun k _ b =>
      let shift := (7 * (n - 1 - k)).toUInt64
      let c := ((v >>> shift) &&& 0x7f).toUInt8
      b.push (if more || k + 1 < n then c ||| 0x80 else c)) b

#guard (List.range 70).all fun k =>
  let vs : List UInt64 := [(1 : UInt64) <<< k.toUInt64, ((1 : UInt64) <<< k.toUInt64) - 1, ((1 : UInt64) <<< k.toUInt64) + 1, 0xFFFFFFFFFFFFFFFF]
  vs.all fun v => let b := putVarint .empty v; getVarint b 0 == (v, b.size) && b.size == varintLen v

end LSql

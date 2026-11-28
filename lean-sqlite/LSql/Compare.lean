import LSql.Record
/-! sqlite's value ordering (datatype3.html §4.1, vdbeaux.c sqlite3MemCompare) and collations, on values and on records. -/
namespace LSql

inductive Collation where
  | binary | nocase | rtrim
  deriving DecidableEq, Repr, Inhabited

def Collation.ofName? (s : String) : Option Collation :=
  match s.toUpper with
  | "BINARY" => some .binary
  | "NOCASE" => some .nocase
  | "RTRIM" => some .rtrim
  | _ => none

/-- Exact comparison of an integer and a real (vdbeaux.c sqlite3IntFloatCompare); NaN compares below every integer. -/
def cmpIntReal (i : Int64) (r : Float) : Ordering :=
  if r.isNaN then .gt
  else if r < -9223372036854775808.0 then .gt
  else if r >= 9223372036854775808.0 then .lt
  else
    let y := r.toInt64
    if i < y then .lt else if i > y then .gt
    else
      let f := r - y.toFloat
      if f > 0 then .lt else if f < 0 then .gt else .eq

@[inline] def cmpFloat (a b : Float) : Ordering :=
  if a < b then .lt else if a > b then .gt else .eq

@[inline] def foldCase (c : UInt8) : UInt8 := if c ≥ 65 && c ≤ 90 then c + 32 else c

/-- Compares bytes `a[ai, ai+an)` and `b[bi, bi+bn)` under a collation (memcmp order; NOCASE folds ASCII; RTRIM ignores trailing spaces). -/
def cmpBytes (coll : Collation) (a : ByteArray) (ai an : Nat) (b : ByteArray) (bi bn : Nat) : Ordering :=
  let n := min an bn
  match go 0 n with
  | .eq =>
    if an == bn then .eq
    else if coll == .rtrim then
      if an < bn then (if allSpaces b (bi + an) (bn - an) then .eq else .lt)
      else (if allSpaces a (ai + bn) (an - bn) then .eq else .gt)
    else compare an bn
  | o => o
where
  go (k : Nat) : Nat → Ordering
    | 0 => .eq
    | f+1 =>
      let x := rd a (ai + k)
      let y := rd b (bi + k)
      let (x, y) := if coll == .nocase then (foldCase x, foldCase y) else (x, y)
      if x < y then .lt else if x > y then .gt else go (k+1) f
  allSpaces (c : ByteArray) (i : Nat) : Nat → Bool
    | 0 => true
    | f+1 => rd c i == 32 && allSpaces c (i+1) f

/-- Compares two strings' UTF-8 bytes in place under a collation (an escaped byte compares as the raw byte). -/
def cmpStrings (coll : Collation) (a b : String) : Ordering :=
  let an := a.utf8ByteSize
  let bn := b.utf8ByteSize
  match go 0 (min an bn) with
  | .eq =>
    if an == bn then .eq
    else if coll == .rtrim then
      if an < bn then (if spaces b an (bn - an) then .eq else .lt)
      else (if spaces a bn (an - bn) then .eq else .gt)
    else compare an bn
  | o => o
where
  go (k : Nat) : Nat → Ordering
    | 0 => .eq
    | f+1 =>
      let x := strByte a k
      let y := strByte b k
      let (x, y) := if coll == .nocase then (foldCase x, foldCase y) else (x, y)
      if x == y then go (k+1) f
      else if (x < 0x80 && y < 0x80) || !(hasEsc a || hasEsc b) then (if x < y then .lt else .gt)
      else cmpBytes coll (textBytes a) 0 (textBytes a).size (textBytes b) 0 (textBytes b).size
  spaces (s : String) (i : Nat) : Nat → Bool
    | 0 => true
    | f+1 => strByte s i == 32 && spaces s (i+1) f

/-- sqlite3MemCompare: NULL < numbers < text < blob; text under the collation. -/
def cmpValues (coll : Collation) : Value → Value → Ordering
  | .null, .null => .eq
  | .null, _ => .lt
  | _, .null => .gt
  | .int a, .int b => compare a b
  | .int a, .real b => cmpIntReal a b
  | .real a, .int b => (cmpIntReal b a).swap
  | .real a, .real b => cmpFloat a b
  | .int _, _ | .real _, _ => .lt
  | _, .int _ | _, .real _ => .gt
  | .text a, .text b => cmpStrings coll a b
  | .text _, .blob _ => .lt
  | .blob _, .text _ => .gt
  | .blob a, .blob b => cmpBytes .binary a 0 a.size b 0 b.size

/-- How an index orders its key fields: one collation and direction per indexed column (the rowid after them is BINARY, ASC). -/
structure KeyInfo where
  colls : Array Collation := #[]
  desc : Array Bool := #[]
  /-- the fields that are the key (a WITHOUT ROWID table's record continues with its other columns) -/
  limit : Nat := 1000000
  deriving Inhabited

/-- The storage class order of a serial type: 0 null, 1 number, 2 text, 3 blob. -/
@[inline] def serialClass (t : UInt64) : Nat :=
  if t == 0 || t == 10 || t == 11 then 0 else if t ≤ 9 then 1 else if t % 2 == 1 then 2 else 3

/-- Compares one field of each record from their serial types and body offsets. -/
def cmpField (coll : Collation) (a : ByteArray) (ta : UInt64) (oa : Nat) (b : ByteArray) (tb : UInt64) (ob : Nat) : Ordering :=
  let ca := serialClass ta
  let cb := serialClass tb
  if ca != cb then compare ca cb
  else match ca with
  | 0 => .eq
  | 1 =>
    if ta == 7 then
      if tb == 7 then cmpFloat (realField a oa) (realField b ob)
      else (cmpIntReal (intField b ob tb) (realField a oa)).swap
    else if tb == 7 then cmpIntReal (intField a oa ta) (realField b ob)
    else compare (intField a oa ta) (intField b ob tb)
  | 2 => cmpBytes coll a oa (serialLen ta) b ob (serialLen tb)
  | _ => cmpBytes .binary a oa (serialLen ta) b ob (serialLen tb)

/-- Compares two index records field by field (a missing field ends the comparison as equal: a probe with fewer fields
matches every entry it is a prefix of). -/
def cmpRecords (ki : KeyInfo) (a b : ByteArray) : Ordering :=
  let (ha, ka) := getVarint a 0
  let (hb, kb) := getVarint b 0
  go ha.toNat hb.toNat ka kb ha.toNat hb.toNat 0 (a.size + 1)
where
  go (ha hb pa pb oa ob i : Nat) : Nat → Ordering
    | 0 => .eq
    | fuel+1 =>
      if pa ≥ ha || pb ≥ hb || i ≥ ki.limit then .eq else
      let (ta, la) := getVarint a pa
      let (tb, lb) := getVarint b pb
      let coll := ki.colls.getD i .binary
      match cmpField coll a ta oa b tb ob with
      | .eq => go ha hb (pa + la) (pb + lb) (oa + serialLen ta) (ob + serialLen tb) (i+1) fuel
      | o => if ki.desc.getD i false then o.swap else o

/-- Compares `a`'s bytes `[ai, ai+an)` with a string's UTF-8 bytes in place under a collation (a string with an escaped byte
is compared by its raw bytes). -/
def cmpBytesString (coll : Collation) (a : ByteArray) (ai an : Nat) (s : String) : Ordering :=
  let bn := s.utf8ByteSize
  match go 0 (min an bn) with
  | .eq =>
    if hasEsc s then (let sb := textBytes s; cmpBytes coll a ai an sb 0 sb.size)
    else if an == bn then .eq
    else if coll == .rtrim then
      if an < bn then (if spaces s an (bn - an) then .eq else .lt)
      else (if allSpaces a (ai + bn) (an - bn) then .eq else .gt)
    else compare an bn
  | o => o
where
  go (k : Nat) : Nat → Ordering
    | 0 => .eq
    | f+1 =>
      let x := rd a (ai + k)
      let y := strByte s k
      let (x, y) := if coll == .nocase then (foldCase x, foldCase y) else (x, y)
      if x == y then go (k+1) f
      else if (x < 0x80 && y < 0x80) || !(hasEsc s) then (if x < y then .lt else .gt)
      else (let sb := textBytes s; cmpBytes coll a ai an sb 0 sb.size)
  spaces (s : String) (i : Nat) : Nat → Bool
    | 0 => true
    | f+1 => strByte s i == 32 && spaces s (i+1) f
  allSpaces (c : ByteArray) (i : Nat) : Nat → Bool
    | 0 => true
    | f+1 => rd c i == 32 && allSpaces c (i+1) f

/-- Compares one field of a record, from its serial type and body offset, with a value. -/
def cmpFieldValue (coll : Collation) (a : ByteArray) (ta : UInt64) (oa : Nat) : Value → Ordering
  | .null => compare (serialClass ta) 0
  | .int y =>
    if serialClass ta != 1 then compare (serialClass ta) 1
    else if ta == 7 then (cmpIntReal y (realField a oa)).swap
    else compare (intField a oa ta) y
  | .real y =>
    if serialClass ta != 1 then compare (serialClass ta) 1
    else if ta == 7 then cmpFloat (realField a oa) y
    else cmpIntReal (intField a oa ta) y
  | .text s => if serialClass ta != 2 then compare (serialClass ta) 2 else cmpBytesString coll a oa (serialLen ta) s
  | .blob y => if serialClass ta != 3 then compare (serialClass ta) 3 else cmpBytes .binary a oa (serialLen ta) y 0 y.size

/-- `cmpRecords ki a b` where `b` is already decoded to `probe` (a search decodes its key once, not once a compare). -/
def cmpRecordProbe (ki : KeyInfo) (a : ByteArray) (probe : Array Value) : Ordering :=
  let (ha, ka) := getVarint a 0
  go ha.toNat ka ha.toNat 0 (a.size + 1)
where
  go (ha pa oa i : Nat) : Nat → Ordering
    | 0 => .eq
    | fuel+1 =>
      if pa ≥ ha || i ≥ probe.size || i ≥ ki.limit then .eq else
      let (ta, la) := getVarint a pa
      match cmpFieldValue (ki.colls.getD i .binary) a ta oa (probe.getD i .null) with
      | .eq => go ha (pa + la) (oa + serialLen ta) (i+1) fuel
      | o => if ki.desc.getD i false then o.swap else o

/-- ORDER BY's order of two key values from whether each is NULL and `cmp`, their order when neither is: NULLs first
or last apart from DESC, the others reversed for DESC. -/
def keyOrder (desc nullsFirst aNull bNull : Bool) (cmp : Unit → Ordering) : Ordering :=
  match aNull, bNull with
  | true, true => .eq
  | true, false => if nullsFirst then .lt else .gt
  | false, true => if nullsFirst then .gt else .lt
  | false, false => let o := cmp (); if desc then o.swap else o

/-- ORDER BY's order on the leading fields of two sort records, one field per key of `dirs` (DESC, NULLS FIRST,
collation), decoding nothing. -/
def cmpSortRecords (dirs : Array (Bool × Bool × Collation)) (a b : ByteArray) : Ordering :=
  let (ha, ka) := getVarint a 0
  let (hb, kb) := getVarint b 0
  go ha.toNat hb.toNat ka kb ha.toNat hb.toNat 0 dirs.size
where
  go (ha hb pa pb oa ob i : Nat) : Nat → Ordering
    | 0 => .eq
    | f+1 =>
      if pa ≥ ha || pb ≥ hb then .eq else
      let (ta, la) := getVarint a pa
      let (tb, lb) := getVarint b pb
      let (desc, nullsFirst, coll) := dirs.getD i (false, true, .binary)
      match keyOrder desc nullsFirst (serialClass ta == 0) (serialClass tb == 0) fun _ => cmpField coll a ta oa b tb ob with
      | .eq => go ha hb (pa + la) (pb + lb) (oa + serialLen ta) (ob + serialLen tb) (i+1) f
      | o => o

/-- `cmpRecords` on the fields' values, for entries not yet encoded: the same order, without decoding. -/
def cmpEntries (ki : KeyInfo) (a b : Array Value) : Ordering :=
  go 0 (min a.size b.size)
where
  go (i : Nat) : Nat → Ordering
    | 0 => .eq
    | fuel+1 =>
      if i ≥ ki.limit then .eq else
      match cmpValues (ki.colls.getD i .binary) (a.getD i .null) (b.getD i .null) with
      | .eq => go (i+1) fuel
      | o => if ki.desc.getD i false then o.swap else o

end LSql

import Std.Data.HashMap

/-! difflib.lua: Python's `difflib.SequenceMatcher(None, a, b, autojunk=False)`, whose exact opcodes the conflict
check depends on. Indices are Python's: 0-based, spans half-open. -/

namespace SwarmLean.Difflib

variable {α : Type} [BEq α] [Hashable α]

/-- Each element of `b` with the indices where it occurs, ascending (no junk, no popular elements). -/
def b2j [Inhabited α] (b : Array α) : Std.HashMap α (Array Nat) := Id.run do
  let mut r : Std.HashMap α (Array Nat) := {}
  for j in [0:b.size] do
    r := r.insert b[j]! ((r.getD b[j]! #[]).push j)
  return r

/-- The longest matching block in `a[alo:ahi]` and `b[blo:bhi]`, the earliest in `a`, then in `b`, on ties:
`(i, j, size)`. -/
def findLongestMatch [Inhabited α] (a b : Array α) (idx : Std.HashMap α (Array Nat)) (alo ahi blo bhi : Nat) :
    Nat × Nat × Nat := Id.run do
  let mut besti := alo
  let mut bestj := blo
  let mut bestsize := 0
  let mut j2len : Std.HashMap Nat Nat := {}
  for i in [alo:ahi] do
    let mut newj2len : Std.HashMap Nat Nat := {}
    for j in idx.getD a[i]! #[] do
      if j < blo then continue
      if j ≥ bhi then break
      let k := (if j == 0 then 0 else j2len.getD (j - 1) 0) + 1
      newj2len := newj2len.insert j k
      if k > bestsize then
        besti := i + 1 - k; bestj := j + 1 - k; bestsize := k
    j2len := newj2len
  -- Python's extension over non-junk neighbours: a no-op without junk, kept as written
  while besti > alo && bestj > blo && a[besti - 1]! == b[bestj - 1]! do
    besti := besti - 1; bestj := bestj - 1; bestsize := bestsize + 1
  while besti + bestsize < ahi && bestj + bestsize < bhi && a[besti + bestsize]! == b[bestj + bestsize]! do
    bestsize := bestsize + 1
  return (besti, bestj, bestsize)

/-- The matching blocks `(i, j, size)`, adjacent ones joined, ending with `(len a, len b, 0)`. -/
def matchingBlocks [Inhabited α] (a b : Array α) : Array (Nat × Nat × Nat) := Id.run do
  let idx := b2j b
  let mut queue : Array (Nat × Nat × Nat × Nat) := #[(0, a.size, 0, b.size)]
  let mut blocks : Array (Nat × Nat × Nat) := #[]
  -- each step takes one span off the queue and adds at most two smaller ones around a nonempty block
  for _ in [0:2 * (a.size + b.size) + 2] do
    let some (alo, ahi, blo, bhi) := queue.back? | break
    queue := queue.pop
    let (i, j, k) := findLongestMatch a b idx alo ahi blo bhi
    if k > 0 then
      blocks := blocks.push (i, j, k)
      if alo < i && blo < j then queue := queue.push (alo, i, blo, j)
      if i + k < ahi && j + k < bhi then queue := queue.push (i + k, ahi, j + k, bhi)
  let sorted := blocks.qsort (·.1 < ·.1)
  let mut out : Array (Nat × Nat × Nat) := #[]
  let mut (i1, j1, k1) := (0, 0, 0)
  for (i2, j2, k2) in sorted do
    if i1 + k1 == i2 && j1 + k1 == j2 then k1 := k1 + k2
    else
      if k1 > 0 then out := out.push (i1, j1, k1)
      (i1, j1, k1) := (i2, j2, k2)
  if k1 > 0 then out := out.push (i1, j1, k1)
  return out.push (a.size, b.size, 0)

/-- `(tag, i1, i2, j1, j2)` rows, tag one of replace, delete, insert, equal. -/
def opcodes [Inhabited α] (a b : Array α) : Array (String × Nat × Nat × Nat × Nat) := Id.run do
  let mut i := 0
  let mut j := 0
  let mut res := #[]
  for (ai, bj, size) in matchingBlocks a b do
    let tag := if i < ai && j < bj then "replace" else if i < ai then "delete" else if j < bj then "insert" else ""
    if tag != "" then res := res.push (tag, i, ai, j, bj)
    i := ai + size; j := bj + size
    if size > 0 then res := res.push ("equal", ai, i, bj, j)
  return res

end SwarmLean.Difflib

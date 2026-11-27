import LSql
import Std.Tactic.BVDecide
/-! Properties of lean-sqlite proved in Lean (checked by `lake build LSqlProofs`; the executable does not import this). -/
namespace LSql.Proofs

/-- Comparison affinity does not depend on which side of the comparison an operand is on. -/
theorem cmpAff_comm (a b : Aff) : cmpAff a b = cmpAff b a := by
  cases a <;> cases b <;> rfl

/-- Comparing a number with anything applies NUMERIC (or the number's own) affinity: a numeric side wins. -/
theorem cmpAff_numeric (a b : Aff) (ha : a.isNumeric) (hb : b ≠ .none) : (cmpAff a b).isNumeric := by
  cases a <;> cases b <;> simp_all [cmpAff, Aff.isNumeric]

/-- Case folding (NOCASE) is idempotent. -/
theorem foldCase_idem (c : UInt8) : foldCase (foldCase c) = foldCase c := by
  unfold foldCase; bv_decide

/-- Case folding leaves no upper-case ASCII letter. -/
theorem foldCase_not_upper (c : UInt8) : ¬ (foldCase c ≥ 65 ∧ foldCase c ≤ 90) := by
  unfold foldCase; bv_decide

/-- Swapping an ordering twice is the identity (ORDER BY ... DESC applied twice). -/
theorem swap_swap (o : Ordering) : o.swap.swap = o := by cases o <;> rfl

/-- The varint length is between 1 and 9 bytes. -/
theorem varintLen_bounds (v : UInt64) : 1 ≤ varintLen v ∧ varintLen v ≤ 9 := by
  unfold varintLen; split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> omega

/-- A cell's slot on a page is never smaller than the 4 bytes sqlite allocates. -/
theorem leafCellBytes_ge (g : Geo) (k : TreeKind) (p e : Nat) : 4 ≤ leafCellBytes g k p e := by
  unfold leafCellBytes; omega

/-- Inserting into a node's arrays adds exactly the inserted elements. -/
theorem insertMany_size {α} (xs ys : Array α) (i : Nat) (hi : i ≤ xs.size) :
    (BTree.insertMany xs i ys).size = xs.size + ys.size := by
  unfold BTree.insertMany
  split
  · next h => simp [Array.insertIdxIfInBounds, hi, h]
  · simp [Array.size_append, Array.size_extract]; omega

/-- The serial type of an integer has a body as long as `serialLen` reads back. -/
theorem serialLen_int (i : Int64) : serialLen (serialType (.int i)).1 = (serialType (.int i)).2 := by
  simp only [serialType]
  split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> simp_all [serialLen]

end LSql.Proofs

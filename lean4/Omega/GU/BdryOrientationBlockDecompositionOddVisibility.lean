import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Int.Basic
import Mathlib.Tactic

namespace Omega.GU

/-- The Koszul sign contributed by swapping two adjacent blocks of cardinalities `a` and `b`. -/
def bdryOrientationSwapSign (a b : ℕ) : ℤ :=
  if Odd (a * b) then -1 else 1

/-- The odd-block visibility correction: it is nontrivial exactly when both blocks are odd. -/
def oddBlockVisibilityCorrection (a b : ℕ) : ℤ :=
  if Odd a ∧ Odd b then -1 else 1

/-- The swap sign corrected by the odd-block visibility torsor. -/
def correctedBlockOrientation (a b : ℕ) : ℤ :=
  bdryOrientationSwapSign a b * oddBlockVisibilityCorrection a b

/-- Adjacent block swaps contribute the Koszul sign `(-1)^(|Sₜ₁||Sₜ₂|)`, and the odd-block index
set provides exactly the same correction, so the corrected orientation class is block-order
independent.  `prop:bdry-orientation-block-decomposition-odd-visibility` -/
theorem paper_bdry_orientation_block_decomposition_odd_visibility (a b : ℕ) :
    bdryOrientationSwapSign a b = oddBlockVisibilityCorrection a b ∧
      correctedBlockOrientation a b = 1 := by
  have hodd : Odd (a * b) ↔ Odd a ∧ Odd b := by
    simpa using (Nat.odd_mul : Odd (a * b) ↔ Odd a ∧ Odd b)
  by_cases h : Odd a ∧ Odd b
  · simp [bdryOrientationSwapSign, oddBlockVisibilityCorrection, correctedBlockOrientation, hodd, h]
  · simp [bdryOrientationSwapSign, oddBlockVisibilityCorrection, correctedBlockOrientation, hodd, h]

end Omega.GU

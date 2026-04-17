import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open Matrix

/-- The symmetric `3 × 3` Gram matrix with unit diagonal and pairwise overlaps `a`, `b`, `c`. -/
def xiGram3 (a b c : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, a, c; a, 1, b; c, b, 1]

/-- The scalar closed form of the `3 × 3` Gram determinant. -/
def xiGram3Det (a b c : ℝ) : ℝ :=
  1 - a ^ 2 - b ^ 2 - c ^ 2 + 2 * a * b * c

lemma xiGram3_det_le_nearestNeighborProduct (a b c : ℝ) :
    xiGram3Det a b c ≤ (1 - a ^ 2) * (1 - b ^ 2) := by
  rw [xiGram3Det]
  nlinarith [sq_nonneg (c - a * b)]

/-- Paper-facing nearest-neighbor product upper bound for the concrete `κ = 3` Gram determinant:
the determinant is bounded above by the product of the two adjacent `2 × 2` defects, hence any
positive determinant yields the corresponding lower bound on `-log det`.
    prop:xi-gram-det-nearest-neighbor-product-upper-bound -/
theorem paper_xi_gram_det_nearest_neighbor_product_upper_bound (a b c : ℝ) :
    xiGram3Det a b c ≤ (1 - a ^ 2) * (1 - b ^ 2) ∧
      (0 < xiGram3Det a b c →
        -Real.log (xiGram3Det a b c) ≥ -Real.log ((1 - a ^ 2) * (1 - b ^ 2))) := by
  refine ⟨xiGram3_det_le_nearestNeighborProduct a b c, ?_⟩
  intro hdet
  have hbound := xiGram3_det_le_nearestNeighborProduct a b c
  have hprod : 0 < (1 - a ^ 2) * (1 - b ^ 2) := lt_of_lt_of_le hdet hbound
  have hlog : Real.log (xiGram3Det a b c) ≤ Real.log ((1 - a ^ 2) * (1 - b ^ 2)) :=
    Real.log_le_log hdet hbound
  exact neg_le_neg hlog

end Omega.Zeta

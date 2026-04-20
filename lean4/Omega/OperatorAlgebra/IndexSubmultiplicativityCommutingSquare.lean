import Mathlib.Tactic

namespace Omega.OperatorAlgebra

/-- In the simplified commuting-square model, a lower bound on the inverse index implies the usual
submultiplicative upper bound on the Jones index.
    prop:op-algebra-index-submultiplicativity-commuting-square -/
theorem paper_op_algebra_index_submultiplicativity_commuting_square {ind1 ind2 ind12 : ℝ}
    (h1 : 0 < ind1) (h2 : 0 < ind2) (h12 : 0 < ind12)
    (hcomp : ind12⁻¹ ≥ ind1⁻¹ * ind2⁻¹) : ind12 ≤ ind1 * ind2 := by
  have hmul :
      ind12⁻¹ * (ind12 * ind1 * ind2) ≥ (ind1⁻¹ * ind2⁻¹) * (ind12 * ind1 * ind2) := by
    exact mul_le_mul_of_nonneg_right hcomp (show 0 ≤ ind12 * ind1 * ind2 by positivity)
  field_simp [h1.ne', h2.ne', h12.ne'] at hmul
  nlinarith

end Omega.OperatorAlgebra

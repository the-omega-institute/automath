import Omega.OperatorAlgebra.PimsnerPopaWitnessBound
import Mathlib.Tactic

namespace Omega.OperatorAlgebra

/-- Reversing the Pimsner-Popa index bound under reciprocals turns a witness-size lower bound on
the worst-case soundness error into the ambient index lower bound.
    cor:op-algebra-soundness-lower-bound-index -/
theorem paper_op_algebra_soundness_lower_bound_index {ind eps : ℝ} {k : ℕ} (hInd : 0 < ind)
    (hk : 0 < k) (hkBound : (k : ℝ) ≤ ind) (hWorst : (k : ℝ)⁻¹ ≤ eps) : ind⁻¹ ≤ eps := by
  have hkR : 0 < (k : ℝ) := by
    exact_mod_cast hk
  have hInv : ind⁻¹ ≤ (k : ℝ)⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le hkR hkBound
  have hIndInv_nonneg : 0 ≤ ind⁻¹ := by
    exact inv_nonneg.mpr (le_of_lt hInd)
  have _ : 0 ≤ eps := le_trans (le_trans hIndInv_nonneg hInv) hWorst
  exact le_trans hInv hWorst

end Omega.OperatorAlgebra

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete endpoint-defect package for one defect: the substitution parameter
`δ² / (1 - δ²)` is positive, the endpoint logarithm collapses to `-2 log δ`, and the resulting
weighted KL factor is positive. -/
def xi_endpoint_single_defect_weighted_kl_li2_statement (δ : ℝ) : Prop :=
  0 < δ ^ 2 ∧
    0 < 1 - δ ^ 2 ∧
    Real.log (1 / δ ^ 2) = -2 * Real.log δ ∧
    0 < (δ ^ 2 / (1 - δ ^ 2)) * Real.log (1 / δ ^ 2)

/-- Paper label: `cor:xi-endpoint-single-defect-weighted-kl-li2`. -/
theorem paper_xi_endpoint_single_defect_weighted_kl_li2
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    xi_endpoint_single_defect_weighted_kl_li2_statement δ := by
  have hδsq_pos : 0 < δ ^ 2 := by positivity
  have hδsq_lt_one : δ ^ 2 < 1 := by nlinarith
  have hone_sub_pos : 0 < 1 - δ ^ 2 := by linarith
  have hδ_ne : δ ≠ 0 := ne_of_gt hδ0
  have hδsq_ne : (δ ^ 2 : ℝ) ≠ 0 := by positivity
  have hlog :
      Real.log (1 / δ ^ 2) = -2 * Real.log δ := by
    calc
      Real.log (1 / δ ^ 2) = Real.log ((δ ^ 2)⁻¹) := by simp [one_div]
      _ = -Real.log (δ ^ 2) := by rw [Real.log_inv]
      _ = -Real.log (δ * δ) := by congr 1; ring
      _ = -(Real.log δ + Real.log δ) := by rw [Real.log_mul hδ_ne hδ_ne]
      _ = -2 * Real.log δ := by ring
  have hinv_gt_one : (1 : ℝ) < 1 / δ ^ 2 := by
    by_contra h
    have hle : 1 / δ ^ 2 ≤ 1 := le_of_not_gt h
    have hmul := mul_le_mul_of_nonneg_left hle (le_of_lt hδsq_pos)
    have hone : (1 : ℝ) ≤ δ ^ 2 := by
      simpa [div_eq_mul_inv, hδsq_ne, mul_comm, mul_left_comm, mul_assoc] using hmul
    linarith
  have hlog_pos : 0 < Real.log (1 / δ ^ 2) := Real.log_pos hinv_gt_one
  have hquot_pos : 0 < δ ^ 2 / (1 - δ ^ 2) := by positivity
  exact ⟨hδsq_pos, hone_sub_pos, hlog, by positivity⟩

end Omega.Zeta

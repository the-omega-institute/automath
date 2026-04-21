import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-single-scale-radial-deviation-arcosh`. For a real root of
`y + y⁻¹ = S` outside the critical interval, the logarithmic radial deviation is the
`arcosh` of `|S| / 2`. -/
theorem paper_xi_single_scale_radial_deviation_arcosh (L S y : ℝ) (hL : 1 < L) (hy0 : y ≠ 0)
    (hy : y + 1 / y = S) (hS : 2 < |S|) :
    |Real.log (|y|) / Real.log L| = Real.arcosh (|S| / 2) / Real.log L := by
  have hy_abs_pos : 0 < |y| := abs_pos.mpr hy0
  have hlogL_pos : 0 < Real.log L := Real.log_pos hL
  have hS_abs : |S| = |y| + 1 / |y| := by
    rw [← hy]
    by_cases hy_nonneg : 0 ≤ y
    · have hy_inv_nonneg : 0 ≤ 1 / y := by
        rw [one_div_nonneg]
        exact hy_nonneg
      rw [abs_of_nonneg (add_nonneg hy_nonneg hy_inv_nonneg), abs_of_nonneg hy_nonneg]
    · have hy_neg : y < 0 := lt_of_not_ge hy_nonneg
      have hy_inv_neg : 1 / y < 0 := (one_div_neg).2 hy_neg
      have hsum_nonpos : y + 1 / y ≤ 0 := by linarith
      rw [abs_of_nonpos hsum_nonpos, abs_of_neg hy_neg]
      field_simp [hy0]
      ring
  have hcosh : Real.cosh (Real.log |y|) = |S| / 2 := by
    calc
      Real.cosh (Real.log |y|) = (|y| + |y|⁻¹) / 2 := Real.cosh_log hy_abs_pos
      _ = (|y| + 1 / |y|) / 2 := by ring
      _ = |S| / 2 := by rw [hS_abs]
  have hcosh_abs : Real.cosh (|Real.log (|y|)|) = |S| / 2 := by
    simpa [Real.cosh_abs] using hcosh
  have harcosh : Real.arcosh (|S| / 2) = |Real.log (|y|)| := by
    rw [← hcosh_abs, Real.arcosh_cosh (abs_nonneg _)]
  calc
    |Real.log (|y|) / Real.log L| = |Real.log (|y|)| / Real.log L := by
      rw [abs_div, abs_of_pos hlogL_pos]
    _ = Real.arcosh (|S| / 2) / Real.log L := by rw [← harcosh]

end Omega.Zeta

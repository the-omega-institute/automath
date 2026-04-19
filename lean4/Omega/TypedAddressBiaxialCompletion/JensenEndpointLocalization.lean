import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace Omega.TypedAddressBiaxialCompletion

/-- The inverse-Cayley endpoint profile is maximized at the left endpoint `θ = π`, where the
denominator attains its minimum value `(1 - ρ)^2`.
    cor:app-jensen-endpoint-localization -/
theorem paper_app_jensen_endpoint_localization {rho theta : ℝ} (hrho0 : 0 < rho)
    (hrho1 : rho < 1) :
    ((1 - rho ^ 2) / (1 + rho ^ 2 + 2 * rho * Real.cos theta) ≤ (1 + rho) / (1 - rho)) ∧
      ((1 - rho ^ 2) / (1 + rho ^ 2 + 2 * rho * Real.cos Real.pi) = (1 + rho) / (1 - rho)) := by
  have hone_sub_pos : 0 < 1 - rho := by linarith
  have hone_sub_ne : 1 - rho ≠ 0 := hone_sub_pos.ne'
  have hnum_nonneg : 0 ≤ 1 - rho ^ 2 := by nlinarith
  have hden_lower : (1 - rho) ^ 2 ≤ 1 + rho ^ 2 + 2 * rho * Real.cos theta := by
    have hcos : -1 ≤ Real.cos theta := Real.neg_one_le_cos theta
    nlinarith
  have hsq_pos : 0 < (1 - rho) ^ 2 := sq_pos_of_ne_zero hone_sub_ne
  have hden_pos : 0 < 1 + rho ^ 2 + 2 * rho * Real.cos theta := by
    linarith
  constructor
  · have hdiv :
        (1 - rho ^ 2) / (1 + rho ^ 2 + 2 * rho * Real.cos theta) ≤
          (1 - rho ^ 2) / (1 - rho) ^ 2 := by
      exact div_le_div_of_nonneg_left hnum_nonneg hsq_pos hden_lower
    have hrhs : (1 - rho ^ 2) / (1 - rho) ^ 2 = (1 + rho) / (1 - rho) := by
      field_simp [hone_sub_ne]
      ring_nf
    calc
      (1 - rho ^ 2) / (1 + rho ^ 2 + 2 * rho * Real.cos theta)
          ≤ (1 - rho ^ 2) / (1 - rho) ^ 2 := hdiv
      _ = (1 + rho) / (1 - rho) := hrhs
  · rw [Real.cos_pi]
    have hnum :
        1 - rho ^ 2 = (1 + rho) * (1 - rho) := by
      ring
    have hden :
        1 + rho ^ 2 + 2 * rho * (-1 : ℝ) = (1 - rho) * (1 - rho) := by
      ring
    rw [hnum, hden, mul_comm (1 + rho) (1 - rho), mul_div_mul_left _ _ hone_sub_ne]

end Omega.TypedAddressBiaxialCompletion

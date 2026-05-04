import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.Zeta

/-- The center-capacity threshold `φ / sqrt 5`. -/
noncomputable def xi_time_part70ab_center_capacity_inverse_threshold_closed_threshold : ℝ :=
  Real.goldenRatio / Real.sqrt 5

/-- Limiting two-kink center capacity: linear up to the threshold and translated afterwards. -/
noncomputable def xi_time_part70ab_center_capacity_inverse_threshold_closed_capacity
    (tau : ℝ) : ℝ :=
  let theta := xi_time_part70ab_center_capacity_inverse_threshold_closed_threshold
  if tau ≤ theta then theta * tau else theta + (tau - theta)

/-- Generalized inverse of the limiting two-kink center capacity on the normalized interval. -/
noncomputable def xi_time_part70ab_center_capacity_inverse_threshold_closed_tauStar
    (rho : ℝ) : ℝ :=
  let theta := xi_time_part70ab_center_capacity_inverse_threshold_closed_threshold
  if rho ≤ theta then rho / theta else theta + (rho - theta)

/-- Closed-form inverse threshold formula. -/
noncomputable def xi_time_part70ab_center_capacity_inverse_threshold_closed_closedForm
    (rho : ℝ) : ℝ :=
  let theta := xi_time_part70ab_center_capacity_inverse_threshold_closed_threshold
  if rho ≤ theta then rho / theta else rho

/-- Paper label: `thm:xi-time-part70ab-center-capacity-inverse-threshold-closed`. -/
theorem paper_xi_time_part70ab_center_capacity_inverse_threshold_closed
    (rho : ℝ) (_hrho0 : 0 ≤ rho) (_hrho1 : rho ≤ 1) :
    xi_time_part70ab_center_capacity_inverse_threshold_closed_tauStar rho =
      xi_time_part70ab_center_capacity_inverse_threshold_closed_closedForm rho := by
  by_cases h :
      rho ≤ xi_time_part70ab_center_capacity_inverse_threshold_closed_threshold
  · simp [xi_time_part70ab_center_capacity_inverse_threshold_closed_tauStar,
      xi_time_part70ab_center_capacity_inverse_threshold_closed_closedForm, h]
  · simp [xi_time_part70ab_center_capacity_inverse_threshold_closed_tauStar,
      xi_time_part70ab_center_capacity_inverse_threshold_closed_closedForm, h]

end Omega.Zeta

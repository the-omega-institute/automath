import Mathlib.Tactic

namespace Omega.UnitCirclePhaseArithmetic

/-- Paper label: `prop:leyang-ellipse-layer-positive-real-crossing`.
Along the radius-`r` circle with `r ≠ 1`, the inverse-square Lee--Yang gate hits a negative real
value at angle `0` and a positive real value at angle `π / 2`. -/
theorem paper_leyang_ellipse_layer_positive_real_crossing
    (r : ℝ) (hr : 0 < r) (hr1 : r ≠ 1) :
    -((r + r⁻¹)^2 : ℝ)⁻¹ < 0 ∧ 0 < ((r - r⁻¹)^2 : ℝ)⁻¹ := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hplus : 0 < r + r⁻¹ := by
    positivity
  have hplus_sq : 0 < (r + r⁻¹) ^ 2 := sq_pos_of_pos hplus
  have hplus_inv : 0 < ((r + r⁻¹)^2 : ℝ)⁻¹ := inv_pos.mpr hplus_sq
  have hsub : r - r⁻¹ ≠ 0 := by
    intro hzero
    have hEq : r = r⁻¹ := sub_eq_zero.mp hzero
    have hsquare : r ^ 2 = 1 := by
      have hmul := congrArg (fun x : ℝ => x * r) hEq
      simpa [pow_two, hr0, mul_comm, mul_left_comm, mul_assoc] using hmul
    have hone : r = 1 := by
      nlinarith [hr, hsquare]
    exact hr1 hone
  have hsub_sq : 0 < (r - r⁻¹) ^ 2 := sq_pos_iff.mpr hsub
  have hsub_inv : 0 < ((r - r⁻¹)^2 : ℝ)⁻¹ := inv_pos.mpr hsub_sq
  exact ⟨by linarith, hsub_inv⟩

end Omega.UnitCirclePhaseArithmetic

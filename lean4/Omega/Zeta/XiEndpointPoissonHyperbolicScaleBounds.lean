import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic
import Omega.Zeta.UnitaryDeterminantZeroUnitCircle

namespace Omega.Zeta

theorem paper_xi_endpoint_poisson_hyperbolic_scale_bounds (a : ℂ) (ha : Complex.abs a < 1) :
    (1 - Complex.abs a) / (1 + Complex.abs a) ≤
        (1 - Complex.abs a ^ 2) / Complex.abs (1 + a) ^ 2 ∧
      (1 - Complex.abs a ^ 2) / Complex.abs (1 + a) ^ 2 ≤
        (1 + Complex.abs a) / (1 - Complex.abs a) := by
  set r : ℝ := Complex.abs a
  have hr_nonneg : 0 ≤ r := by
    simp [r]
  have hr_lt_one : r < 1 := by
    simpa [r] using ha
  have h_one_sub_pos : 0 < 1 - r := by
    linarith
  have h_one_add_pos : 0 < 1 + r := by
    linarith
  have hupper_abs : Complex.abs (1 + a) ≤ 1 + r := by
    simpa [r] using norm_add_le (1 : ℂ) a
  have htriangle : (1 : ℝ) ≤ Complex.abs (1 + a) + r := by
    simpa [r, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (norm_add_le (1 + a : ℂ) (-a))
  have hlower_abs : 1 - r ≤ Complex.abs (1 + a) := by
    linarith
  have habs_pos : 0 < Complex.abs (1 + a) := by
    exact lt_of_lt_of_le h_one_sub_pos hlower_abs
  have hupper_sq : Complex.abs (1 + a) ^ 2 ≤ (1 + r) ^ 2 := by
    exact (sq_le_sq₀ (by positivity) h_one_add_pos.le).2 hupper_abs
  have hlower_sq : (1 - r) ^ 2 ≤ Complex.abs (1 + a) ^ 2 := by
    exact (sq_le_sq₀ h_one_sub_pos.le (by positivity)).2 hlower_abs
  have hleft :
      (1 - r) / (1 + r) ≤ (1 - r ^ 2) / Complex.abs (1 + a) ^ 2 := by
    have hden_pos : 0 < Complex.abs (1 + a) ^ 2 := by
      positivity
    rw [div_le_div_iff₀ h_one_add_pos hden_pos]
    nlinarith [hupper_sq]
  have hright :
      (1 - r ^ 2) / Complex.abs (1 + a) ^ 2 ≤ (1 + r) / (1 - r) := by
    have hden_pos : 0 < Complex.abs (1 + a) ^ 2 := by
      positivity
    rw [div_le_div_iff₀ hden_pos h_one_sub_pos]
    nlinarith [hlower_sq]
  simpa [r] using ⟨hleft, hright⟩

end Omega.Zeta

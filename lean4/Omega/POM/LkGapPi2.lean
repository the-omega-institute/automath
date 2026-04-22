import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `cor:pom-Lk-gap-pi2`. The first two spectral points of `L_k` come from the
angles `π / (4k + 2)` and `3π / (4k + 2)`, and `sin` is strictly increasing on `(0, π / 2)`. -/
theorem paper_pom_lk_gap_pi2 (k : Nat) (hk : 2 ≤ k) :
    4 * Real.sin (Real.pi / (4 * k + 2)) ^ 2 < 4 * Real.sin (3 * Real.pi / (4 * k + 2)) ^ 2 := by
  have hk' : (6 : ℝ) ≤ 4 * k + 2 := by
    exact_mod_cast (show 6 ≤ 4 * k + 2 by omega)
  have hden_pos : (0 : ℝ) < 4 * k + 2 := by
    linarith
  have hx_pos : 0 < Real.pi / (4 * k + 2 : ℝ) := by
    positivity
  have hxy :
      Real.pi / (4 * k + 2 : ℝ) < 3 * Real.pi / (4 * k + 2 : ℝ) := by
    refine (div_lt_div_iff_of_pos_right hden_pos).2 ?_
    nlinarith [Real.pi_pos]
  have hfrac : (3 : ℝ) / (4 * k + 2 : ℝ) ≤ 1 / 2 := by
    rw [div_le_iff₀ hden_pos]
    nlinarith [hk']
  have hy_le : 3 * Real.pi / (4 * k + 2 : ℝ) ≤ Real.pi / 2 := by
    have := mul_le_mul_of_nonneg_right hfrac Real.pi_pos.le
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
  have hy_pos : 0 < 3 * Real.pi / (4 * k + 2 : ℝ) := by
    positivity
  have hy_lt_pi : 3 * Real.pi / (4 * k + 2 : ℝ) < Real.pi := by
    nlinarith [Real.pi_pos, hy_le]
  have hx_lt_pi : Real.pi / (4 * k + 2 : ℝ) < Real.pi := by
    exact lt_trans hxy hy_lt_pi
  have hsin_lt :
      Real.sin (Real.pi / (4 * k + 2 : ℝ)) < Real.sin (3 * Real.pi / (4 * k + 2 : ℝ)) := by
    apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
    · nlinarith [hx_pos]
    · exact hy_le
    · exact hxy
  have hsq :
      Real.sin (Real.pi / (4 * k + 2 : ℝ)) ^ 2 < Real.sin (3 * Real.pi / (4 * k + 2 : ℝ)) ^ 2 := by
    refine (sq_lt_sq₀ ?_ ?_).2 hsin_lt
    · exact le_of_lt (Real.sin_pos_of_pos_of_lt_pi hx_pos hx_lt_pi)
    · exact le_of_lt (Real.sin_pos_of_pos_of_lt_pi hy_pos hy_lt_pi)
  exact mul_lt_mul_of_pos_left hsq (by norm_num)

end Omega.POM

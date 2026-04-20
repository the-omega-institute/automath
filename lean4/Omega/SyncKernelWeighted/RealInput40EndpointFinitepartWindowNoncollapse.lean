import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

/-- On the quartic-root window `3 < y < 4`, the reciprocal parameter `b = 1 / y` lies between
`1 / 4` and `1 / 3`; the endpoint constant already satisfies `C∞ > 1`; and positivity of the
finite-part logarithm forces `exp(log M∞) > 1`.
    cor:real-input-40-zeta-u-endpoint-finitepart-window-noncollapse -/
theorem paper_real_input_40_zeta_u_endpoint_finitepart_window_noncollapse
    {b Cinf logMinf y : ℝ}
    (hy : 3 < y ∧ y < 4)
    (hb : b = 1 / y)
    (hC : 1 < Cinf)
    (hlogM : 0 < logMinf) :
    1 / 4 < b ∧ b < 1 / 3 ∧ 1 < Cinf ∧ 1 < Real.exp logMinf := by
  rcases hy with ⟨hy3, hy4⟩
  have hy_pos : 0 < y := lt_trans (by norm_num) hy3
  have hb_lower : 1 / 4 < b := by
    rw [hb]
    simpa using (one_div_lt_one_div_of_lt hy_pos hy4)
  have hb_upper : b < 1 / 3 := by
    rw [hb]
    have hthree_pos : (0 : ℝ) < 3 := by norm_num
    simpa using (one_div_lt_one_div_of_lt hthree_pos hy3)
  have hexp : 1 < Real.exp logMinf := by
    simpa using (Real.exp_lt_exp.mpr hlogM)
  exact ⟨hb_lower, hb_upper, hC, hexp⟩

end Omega.SyncKernelWeighted

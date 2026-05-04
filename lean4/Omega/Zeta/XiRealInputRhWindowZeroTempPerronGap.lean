import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-real-input-rh-window-zero-temp-perron-gap`. -/
theorem paper_xi_real_input_rh_window_zero_temp_perron_gap
    (uR yInf : ℝ) (hu_lo : (359 : ℝ) / 100 < uR)
    (hu_hi : uR < (3593 : ℝ) / 1000) (hy_lo : (3593 : ℝ) / 1000 < yInf)
    (hy_hi : yInf < (18 : ℝ) / 5) :
    (359 : ℝ) / 100 < uR ∧
      uR < (3593 : ℝ) / 1000 ∧
        (3593 : ℝ) / 1000 < yInf ∧ yInf < (18 : ℝ) / 5 ∧ uR < yInf := by
  exact ⟨hu_lo, hu_hi, hy_lo, hy_hi, lt_trans hu_hi hy_lo⟩

end Omega.Zeta

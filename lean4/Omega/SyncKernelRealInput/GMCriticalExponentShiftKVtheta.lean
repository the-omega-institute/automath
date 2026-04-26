import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

/-- Paper label: `prop:gm-critical-exponent-shift-k-vtheta`. The explicit shift parameter
`Delta = (2k / (2k + 1)) * (vartheta / 10)` is positive as soon as `vartheta` is, and the factor
`2k / (2k + 1)` always lies strictly between `0` and `1` for `k ≥ 1`. -/
theorem paper_gm_critical_exponent_shift_k_vtheta (k : ℕ) (hk : 1 ≤ k) (vartheta : ℝ) :
    let Delta := ((2 : ℝ) * k) / (2 * k + 1) * (vartheta / 10)
    0 < vartheta → 0 < Delta ∧ Delta < vartheta / 10 := by
  dsimp
  intro hvartheta
  have hk_pos : 0 < (k : ℝ) := by
    exact_mod_cast (show 0 < k by omega)
  have hden_pos : 0 < 2 * (k : ℝ) + 1 := by
    nlinarith
  have hfactor_pos : 0 < ((2 : ℝ) * k) / (2 * k + 1) := by
    apply div_pos
    · nlinarith
    · exact hden_pos
  have hfactor_lt_one : ((2 : ℝ) * k) / (2 * k + 1) < 1 := by
    have hden_ne : 2 * (k : ℝ) + 1 ≠ 0 := by
      nlinarith
    field_simp [hden_ne]
    nlinarith
  have hvartheta_tenth_pos : 0 < vartheta / 10 := by
    nlinarith
  constructor
  · exact mul_pos hfactor_pos hvartheta_tenth_pos
  · have hscaled :
        (vartheta / 10) * (((2 : ℝ) * k) / (2 * k + 1)) < vartheta / 10 := by
        exact mul_lt_of_lt_one_right hvartheta_tenth_pos hfactor_lt_one
    simpa [mul_comm] using hscaled

end Omega.SyncKernelRealInput

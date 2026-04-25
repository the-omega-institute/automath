import Mathlib

namespace Omega.Zeta

set_option linter.unusedVariables false in
/-- Paper label: `cor:xi-reversekl-single-frequency-closed-lower`. -/
theorem paper_xi_reversekl_single_frequency_closed_lower {n : ℕ} (hn : 1 ≤ n)
    {r mu2 Hr : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hmu0 : 0 ≤ mu2) (hmu1 : mu2 ≤ 1)
    (harg : 0 < 1 - r ^ (2 * n) * mu2)
    (hHr : -Real.log (1 - r ^ (2 * n) * mu2) ≤ Hr) :
    mu2 ≤ (r ^ (2 * n))⁻¹ * (1 - Real.exp (-Hr)) := by
  clear hn hr1 hmu0 hmu1
  let a : ℝ := r ^ (2 * n)
  have ha_pos : 0 < a := by
    dsimp [a]
    exact pow_pos hr0 _
  have ha_nonneg : 0 ≤ a⁻¹ := inv_nonneg.mpr (le_of_lt ha_pos)
  have hneg : -Hr ≤ Real.log (1 - a * mu2) := by
    dsimp [a] at hHr ⊢
    linarith
  have hexp_le : Real.exp (-Hr) ≤ 1 - a * mu2 := by
    calc
      Real.exp (-Hr) ≤ Real.exp (Real.log (1 - a * mu2)) :=
        Real.exp_le_exp.mpr hneg
      _ = 1 - a * mu2 := by
        dsimp [a] at harg ⊢
        exact Real.exp_log harg
  have hmul_le : a * mu2 ≤ 1 - Real.exp (-Hr) := by
    linarith
  have hane : a ≠ 0 := ne_of_gt ha_pos
  calc
    mu2 = a⁻¹ * (a * mu2) := by
      rw [← mul_assoc, inv_mul_cancel₀ hane, one_mul]
    _ ≤ a⁻¹ * (1 - Real.exp (-Hr)) :=
      mul_le_mul_of_nonneg_left hmul_le ha_nonneg

end Omega.Zeta

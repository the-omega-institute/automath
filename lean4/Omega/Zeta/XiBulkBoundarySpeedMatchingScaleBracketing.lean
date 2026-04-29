import Mathlib.Tactic
import Omega.Zeta.XiBulkBoundarySpeedMatching

namespace Omega.Zeta

noncomputable section

/-- Paper label: `cor:xi-bulk-boundary-speed-matching-scale-bracketing`. -/
theorem paper_xi_bulk_boundary_speed_matching_scale_bracketing (κ : ℕ) (sStar δmin δbar : ℝ)
    (hκ : 1 < κ) (hδmin : 0 < δmin) (hδbar : 0 < δbar)
    (hLower : (1 + Real.exp sStar * δbar)⁻¹ ≤ ((κ : ℝ) - 1) / (2 * (κ : ℝ) - 1))
    (hUpper : ((κ : ℝ) - 1) / (2 * (κ : ℝ) - 1) ≤
      (1 + Real.exp sStar * δmin)⁻¹) :
    (κ : ℝ) / (((κ : ℝ) - 1) * δbar) ≤ Real.exp sStar ∧
      Real.exp sStar ≤ (κ : ℝ) / (((κ : ℝ) - 1) * δmin) := by
  have hk_pos : 0 < (κ : ℝ) := by exact_mod_cast (lt_trans Nat.zero_lt_one hκ)
  have hk_sub_pos : 0 < (κ : ℝ) - 1 := by
    have hk_one : (1 : ℝ) < κ := by exact_mod_cast hκ
    linarith
  have hden_pos : 0 < 2 * (κ : ℝ) - 1 := by nlinarith
  have hx_pos : 0 < Real.exp sStar := Real.exp_pos sStar
  have hbar_den_pos : 0 < 1 + Real.exp sStar * δbar := by positivity
  have hmin_den_pos : 0 < 1 + Real.exp sStar * δmin := by positivity
  constructor
  · have hcross :
        2 * (κ : ℝ) - 1 ≤ ((κ : ℝ) - 1) * (1 + Real.exp sStar * δbar) := by
      have h1 :
          1 ≤ (((κ : ℝ) - 1) / (2 * (κ : ℝ) - 1)) *
            (1 + Real.exp sStar * δbar) := by
        exact (div_le_iff₀ hbar_den_pos).1 (by simpa [one_div] using hLower)
      have h2 :
          1 ≤ (((κ : ℝ) - 1) * (1 + Real.exp sStar * δbar)) /
            (2 * (κ : ℝ) - 1) := by
        convert h1 using 1
        ring
      have h3 := (le_div_iff₀ hden_pos).1 h2
      nlinarith
    have hscaled : (κ : ℝ) ≤ ((κ : ℝ) - 1) * δbar * Real.exp sStar := by
      nlinarith
    exact (div_le_iff₀ (mul_pos hk_sub_pos hδbar)).2 (by
      nlinarith [hscaled])
  · have hcross :
        ((κ : ℝ) - 1) * (1 + Real.exp sStar * δmin) ≤ 2 * (κ : ℝ) - 1 := by
      have h1 :
          (((κ : ℝ) - 1) / (2 * (κ : ℝ) - 1)) *
              (1 + Real.exp sStar * δmin) ≤ 1 := by
        exact (le_div_iff₀ hmin_den_pos).1 (by simpa [one_div] using hUpper)
      have h2 :
          (((κ : ℝ) - 1) * (1 + Real.exp sStar * δmin)) /
              (2 * (κ : ℝ) - 1) ≤ 1 := by
        convert h1 using 1
        ring
      have h3 := (div_le_iff₀ hden_pos).1 h2
      nlinarith
    have hscaled : ((κ : ℝ) - 1) * δmin * Real.exp sStar ≤ (κ : ℝ) := by
      nlinarith
    exact (le_div_iff₀ (mul_pos hk_sub_pos hδmin)).2 (by
      nlinarith [hscaled])

end

end Omega.Zeta

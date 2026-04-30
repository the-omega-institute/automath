import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `con:xi-grid-scan-aliasing-threshold`. -/
theorem paper_xi_grid_scan_aliasing_threshold {Delta T : ℝ}
    (hDelta : 0 < Delta) (hT : 0 < T) :
    (∀ gamma : ℝ, ∀ k : ℤ, ∃ gamma' : ℝ,
      gamma' = gamma + (2 * Real.pi * k) / Delta) ∧
    (Delta < Real.pi / T →
      ∀ gamma gamma' : ℝ, -T ≤ gamma → gamma ≤ T → -T ≤ gamma' → gamma' ≤ T →
        (∃ k : ℤ, gamma' = gamma + (2 * Real.pi * k) / Delta) → gamma' = gamma) := by
  constructor
  · intro gamma k
    exact ⟨gamma + (2 * Real.pi * k) / Delta, rfl⟩
  · intro hWindow gamma gamma' hgamma_lower hgamma_upper hgamma'_lower hgamma'_upper halias
    rcases halias with ⟨k, hk⟩
    by_cases hk_zero : k = 0
    · subst k
      simpa [hDelta.ne'] using hk
    · have hdiam_upper : gamma' - gamma ≤ 2 * T := by linarith
      have hdiam_lower : -(2 * T) ≤ gamma' - gamma := by linarith
      have hmul : Delta * T < Real.pi := by
        exact (lt_div_iff₀ hT).mp hWindow
      have htwoT_lt_shift : 2 * T < (2 * Real.pi) / Delta := by
        exact (lt_div_iff₀ hDelta).mpr (by nlinarith [hmul])
      have hk_cases : k ≤ -1 ∨ 1 ≤ k := by omega
      have hdiff : gamma' - gamma = (2 * Real.pi * (k : ℝ)) / Delta := by
        linarith
      rcases hk_cases with hk_neg | hk_pos
      · have hkR : (k : ℝ) ≤ -1 := by exact_mod_cast hk_neg
        have hshift_le :
            (2 * Real.pi * (k : ℝ)) / Delta ≤ (2 * Real.pi * (-1 : ℝ)) / Delta := by
          apply div_le_div_of_nonneg_right
          · nlinarith [Real.pi_pos, hkR]
          · exact le_of_lt hDelta
        have hneg_base : (2 * Real.pi * (-1 : ℝ)) / Delta < -(2 * T) := by
          have hneg : -((2 * Real.pi) / Delta) < -(2 * T) := by linarith
          convert hneg using 1
          ring
        have hshift_lt : gamma' - gamma < -(2 * T) := by
          calc
            gamma' - gamma = (2 * Real.pi * (k : ℝ)) / Delta := hdiff
            _ ≤ (2 * Real.pi * (-1 : ℝ)) / Delta := hshift_le
            _ < -(2 * T) := hneg_base
        linarith
      · have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk_pos
        have hbase_le :
            (2 * Real.pi) / Delta ≤ (2 * Real.pi * (k : ℝ)) / Delta := by
          apply div_le_div_of_nonneg_right
          · nlinarith [Real.pi_pos, hkR]
          · exact le_of_lt hDelta
        have hshift_gt : 2 * T < gamma' - gamma := by
          calc
            2 * T < (2 * Real.pi) / Delta := htwoT_lt_shift
            _ ≤ (2 * Real.pi * (k : ℝ)) / Delta := hbase_le
            _ = gamma' - gamma := hdiff.symm
        linarith

end Omega.Zeta

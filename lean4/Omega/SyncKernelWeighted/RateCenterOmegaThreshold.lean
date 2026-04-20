import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
import Omega.SyncKernelWeighted.RateCenterRstarJetComplexity

namespace Omega.SyncKernelWeighted

noncomputable section

/-- If the seventh unit-root distance lies strictly inside the `R⋆` radius, then every larger
prime unit-root distance also lies strictly inside that radius, while the fifth unit-root distance
remains outside by the existing `R⋆` package.
    cor:rate-center-omega-threshold -/
theorem paper_rate_center_omega_threshold (D : Omega.SyncKernelWeighted.RateCenterRstarJetComplexityData)
    (hseven : 2 * Real.sin (Real.pi / 7) < D.Rstar) :
    D.Rstar < 2 * Real.sin (Real.pi / 5) ∧ ∀ p : ℕ, 7 ≤ p → 2 * Real.sin (Real.pi / p) < D.Rstar := by
  refine ⟨D.orderFiveOutside_h, ?_⟩
  intro p hp
  have hpR : (0 : ℝ) < p := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 7) hp)
  have hpi_div_le : Real.pi / (p : ℝ) ≤ Real.pi / 7 := by
    rw [div_le_div_iff₀ hpR (by norm_num : (0 : ℝ) < 7)]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hp) Real.pi_pos.le
  have hpi_div_seven_le_half : Real.pi / 7 ≤ Real.pi / 2 := by
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 7) (by norm_num : (0 : ℝ) < 2)]
    linarith [Real.pi_pos]
  have hsin_le : Real.sin (Real.pi / (p : ℝ)) ≤ Real.sin (Real.pi / 7) := by
    apply Real.sin_le_sin_of_le_of_le_pi_div_two
    · have hpos : 0 < Real.pi / (p : ℝ) := div_pos Real.pi_pos hpR
      linarith
    · exact hpi_div_seven_le_half
    · exact hpi_div_le
  have hmul_le : 2 * Real.sin (Real.pi / (p : ℝ)) ≤ 2 * Real.sin (Real.pi / 7) := by
    gcongr
  exact lt_of_le_of_lt hmul_le hseven

end

end Omega.SyncKernelWeighted

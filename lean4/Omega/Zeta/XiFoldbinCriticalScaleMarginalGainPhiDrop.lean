import Mathlib.Tactic
import Omega.Zeta.XiFoldbinCriticalScaleSuccessCurveInversion

namespace Omega.Zeta

noncomputable section

/-- Paper label: `cor:xi-foldbin-critical-scale-marginal-gain-phi-drop`. -/
theorem paper_xi_foldbin_critical_scale_marginal_gain_phi_drop :
    ((∀ s : ℝ, 0 < s → s < Real.goldenRatio⁻¹ →
        xi_foldbin_critical_scale_success_curve_inversion_success_curve s =
          Real.goldenRatio ^ 2 / Real.sqrt 5 * s) ∧
      (∀ s : ℝ, Real.goldenRatio⁻¹ < s → s < 1 →
        xi_foldbin_critical_scale_success_curve_inversion_success_curve s =
          Real.goldenRatio / Real.sqrt 5 * s + (Real.goldenRatio * Real.sqrt 5)⁻¹) ∧
      ((Real.goldenRatio ^ 2 / Real.sqrt 5) / (Real.goldenRatio / Real.sqrt 5) =
        Real.goldenRatio)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s _hs0 hs
    unfold xi_foldbin_critical_scale_success_curve_inversion_success_curve
    rw [if_pos (le_of_lt hs)]
  · intro s hs h1
    unfold xi_foldbin_critical_scale_success_curve_inversion_success_curve
    rw [if_neg (not_le_of_gt hs), if_pos (le_of_lt h1)]
  · have hsqrt : Real.sqrt 5 ≠ 0 := by positivity
    have hphi : Real.goldenRatio ≠ 0 := by positivity
    field_simp [hsqrt, hphi]

end

end Omega.Zeta

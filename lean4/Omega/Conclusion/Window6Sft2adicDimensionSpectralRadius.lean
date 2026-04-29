import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete finite window-6 SFT package for the 2-adic dimension readout.  The growth
and cylinder fields record the finite-window certificate, while the two logarithmic
inequalities are the upper cylinder-cover and lower Frostman/Parry-measure witnesses
needed to place the resulting dimension in the ambient `[0, 2]` range. -/
structure conclusion_window6_sft_2adic_dimension_spectral_radius_data where
  pathCountGrowth : ℝ
  cylinderDiameterScale : ℝ
  spectralRadius : ℝ
  cylinderDiameterScale_eq : cylinderDiameterScale = 8
  pathCountGrowth_eq_logSpectralRadius : pathCountGrowth = Real.log spectralRadius
  spectralRadius_log_nonneg : 0 ≤ Real.log spectralRadius
  spectralRadius_log_le_two_log8 : Real.log spectralRadius ≤ 2 * Real.log 8

namespace conclusion_window6_sft_2adic_dimension_spectral_radius_data

/-- Hausdorff dimension read from the spectral radius at the window-6 2-adic scale. -/
noncomputable def hausdorffDim
    (D : conclusion_window6_sft_2adic_dimension_spectral_radius_data) : ℝ :=
  Real.log D.spectralRadius / Real.log 8

end conclusion_window6_sft_2adic_dimension_spectral_radius_data

/-- Paper label: `thm:conclusion-window6-sft-2adic-dimension-spectral-radius`. -/
theorem paper_conclusion_window6_sft_2adic_dimension_spectral_radius
    (D : conclusion_window6_sft_2adic_dimension_spectral_radius_data) :
    D.hausdorffDim = Real.log D.spectralRadius / Real.log 8 ∧
      0 ≤ D.hausdorffDim ∧ D.hausdorffDim ≤ 2 := by
  have hlog8_pos : 0 < Real.log (8 : ℝ) := Real.log_pos (by norm_num)
  refine ⟨rfl, ?_, ?_⟩
  · exact div_nonneg D.spectralRadius_log_nonneg hlog8_pos.le
  · rw [conclusion_window6_sft_2adic_dimension_spectral_radius_data.hausdorffDim]
    rw [div_le_iff₀ hlog8_pos]
    simpa [mul_comm] using D.spectralRadius_log_le_two_log8

end Omega.Conclusion

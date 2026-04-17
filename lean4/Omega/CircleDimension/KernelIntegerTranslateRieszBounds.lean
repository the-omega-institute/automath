import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Closed-form symbol of the integer-translate Gram convolution for the Cauchy kernel
`K(a, b) = 2 / (4 + (a - b)^2)`. -/
noncomputable def kernelIntegerTranslateSymbol (θ : ℝ) : ℝ :=
  Real.pi * Real.cosh (2 * (Real.pi - |θ|)) / Real.sinh (2 * Real.pi)

/-- Sharp lower Riesz bound coming from the minimum of the symbol on `[-π, π]`. -/
noncomputable def kernelIntegerTranslateLowerBound : ℝ :=
  Real.pi / Real.sinh (2 * Real.pi)

/-- Sharp upper Riesz bound coming from the maximum of the symbol on `[-π, π]`. -/
noncomputable def kernelIntegerTranslateUpperBound : ℝ :=
  Real.pi * Real.cosh (2 * Real.pi) / Real.sinh (2 * Real.pi)

/-- Paper-facing exact Riesz bounds for the integer translates of the CircleDimension kernel:
the closed-form symbol stays between its endpoint values on `[-π, π]`, and the endpoints realize
the sharp lower/upper bounds.
    prop:cdim-kernel-integer-translate-riesz-bounds -/
theorem paper_cdim_kernel_integer_translate_riesz_bounds :
    (∀ θ ∈ Set.Icc (-Real.pi) Real.pi,
      kernelIntegerTranslateLowerBound ≤ kernelIntegerTranslateSymbol θ ∧
        kernelIntegerTranslateSymbol θ ≤ kernelIntegerTranslateUpperBound) ∧
      kernelIntegerTranslateSymbol Real.pi = kernelIntegerTranslateLowerBound ∧
      kernelIntegerTranslateSymbol 0 = kernelIntegerTranslateUpperBound := by
  refine ⟨?_, ?_, ?_⟩
  · intro θ hθ
    rcases hθ with ⟨hθ_left, hθ_right⟩
    have habs : |θ| ≤ Real.pi := by
      rw [abs_le]
      constructor
      · linarith
      · linarith
    have hsub_nonneg : 0 ≤ Real.pi - |θ| := sub_nonneg.mpr habs
    have hsub_le : Real.pi - |θ| ≤ Real.pi := by
      nlinarith [abs_nonneg θ]
    have hdouble_nonneg : 0 ≤ 2 * (Real.pi - |θ|) := by nlinarith
    have hdouble_le : 2 * (Real.pi - |θ|) ≤ 2 * Real.pi := by nlinarith
    have hcosh_upper : Real.cosh (2 * (Real.pi - |θ|)) ≤ Real.cosh (2 * Real.pi) := by
      apply (Real.cosh_le_cosh).2
      simpa [abs_of_nonneg hdouble_nonneg, abs_of_nonneg (show 0 ≤ 2 * Real.pi by positivity)] using
        hdouble_le
    have hsinh_pos : 0 < Real.sinh (2 * Real.pi) := by
      simpa using (Real.sinh_pos_iff.mpr (by positivity : 0 < 2 * Real.pi))
    have hlower_num : Real.pi ≤ Real.pi * Real.cosh (2 * (Real.pi - |θ|)) := by
      have hcosh_lower : 1 ≤ Real.cosh (2 * (Real.pi - |θ|)) := Real.one_le_cosh _
      nlinarith [Real.pi_pos, hcosh_lower]
    have hupper_num :
        Real.pi * Real.cosh (2 * (Real.pi - |θ|)) ≤ Real.pi * Real.cosh (2 * Real.pi) := by
      nlinarith [Real.pi_pos, hcosh_upper]
    constructor
    · exact div_le_div_of_nonneg_right hlower_num hsinh_pos.le
    · exact div_le_div_of_nonneg_right hupper_num hsinh_pos.le
  · simpa [kernelIntegerTranslateSymbol, kernelIntegerTranslateLowerBound,
      abs_of_nonneg (le_of_lt Real.pi_pos)]
  · simp [kernelIntegerTranslateSymbol, kernelIntegerTranslateUpperBound]

end Omega.CircleDimension

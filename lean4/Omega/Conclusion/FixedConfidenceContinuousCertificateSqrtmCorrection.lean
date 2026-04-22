import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete quadratic local model for the fixed-confidence continuous certificate correction. The
rate function is normalized to have unique zero at `gammaStar` and curvature `curvature`; the
parameter `gammaM` is chosen so that the quadratic rate exactly matches the log-budget
`log (1 / epsilon) / m`. -/
structure FixedConfidenceContinuousCertificateSqrtmCorrectionData where
  epsilon : ℝ
  curvature : ℝ
  m : ℕ
  gammaStar : ℝ
  epsilon_pos : 0 < epsilon
  epsilon_lt_one : epsilon < 1
  curvature_pos : 0 < curvature
  m_pos : 0 < m

namespace FixedConfidenceContinuousCertificateSqrtmCorrectionData

/-- Log-budget carried by confidence level `epsilon`. -/
noncomputable def logBudget (D : FixedConfidenceContinuousCertificateSqrtmCorrectionData) : ℝ :=
  Real.log (1 / D.epsilon)

/-- The leading `m^{-1/2}` correction term. -/
noncomputable def sqrtCorrection (D : FixedConfidenceContinuousCertificateSqrtmCorrectionData) :
    ℝ :=
  Real.sqrt (2 * D.logBudget / (D.curvature * (D.m : ℝ)))

/-- Corrected certificate parameter at budget `m`. -/
noncomputable def gammaM (D : FixedConfidenceContinuousCertificateSqrtmCorrectionData) : ℝ :=
  D.gammaStar + D.sqrtCorrection

/-- Local quadratic model for the rate function near its unique zero. -/
noncomputable def rateFunction (D : FixedConfidenceContinuousCertificateSqrtmCorrectionData)
    (γ : ℝ) : ℝ :=
  (D.curvature / 2) * (γ - D.gammaStar) ^ 2

/-- Explicit `m^{-1/2}` expansion of the corrected certificate parameter. -/
def gammaExpansion (D : FixedConfidenceContinuousCertificateSqrtmCorrectionData) : Prop :=
  D.gammaM = D.gammaStar + D.sqrtCorrection

/-- Rewriting the quadratic inversion identity as a log-budget equality. -/
def logBudgetExpansion (D : FixedConfidenceContinuousCertificateSqrtmCorrectionData) : Prop :=
  D.rateFunction D.gammaM = D.logBudget / (D.m : ℝ)

end FixedConfidenceContinuousCertificateSqrtmCorrectionData

open FixedConfidenceContinuousCertificateSqrtmCorrectionData

/-- In the quadratic local regime, solving `I(γ_m) = log(1 / ε) / m` yields an explicit
`m^{-1/2}` correction and the corresponding log-budget expansion.
    thm:conclusion-fixed-confidence-continuous-certificate-sqrtm-correction -/
theorem paper_conclusion_fixed_confidence_continuous_certificate_sqrtm_correction
    (D : FixedConfidenceContinuousCertificateSqrtmCorrectionData) :
    D.gammaExpansion ∧ D.logBudgetExpansion := by
  refine ⟨rfl, ?_⟩
  have hm_pos : 0 < (D.m : ℝ) := by
    exact_mod_cast D.m_pos
  have hcurv_ne : D.curvature ≠ 0 := ne_of_gt D.curvature_pos
  have hm_ne : (D.m : ℝ) ≠ 0 := ne_of_gt hm_pos
  have hbudget_nonneg : 0 ≤ D.logBudget := by
    unfold FixedConfidenceContinuousCertificateSqrtmCorrectionData.logBudget
    apply Real.log_nonneg
    exact le_of_lt ((one_lt_div D.epsilon_pos).2 D.epsilon_lt_one)
  have hsqrt_arg_nonneg :
      0 ≤ 2 * D.logBudget / (D.curvature * (D.m : ℝ)) := by
    refine div_nonneg ?_ (mul_nonneg D.curvature_pos.le hm_pos.le)
    nlinarith
  have hsq :
      D.sqrtCorrection ^ 2 = 2 * D.logBudget / (D.curvature * (D.m : ℝ)) := by
    unfold FixedConfidenceContinuousCertificateSqrtmCorrectionData.sqrtCorrection
    rw [Real.sq_sqrt hsqrt_arg_nonneg]
  calc
    D.rateFunction D.gammaM
        = (D.curvature / 2) * D.sqrtCorrection ^ 2 := by
            unfold FixedConfidenceContinuousCertificateSqrtmCorrectionData.rateFunction
            unfold FixedConfidenceContinuousCertificateSqrtmCorrectionData.gammaM
            ring
    _ = (D.curvature / 2) * (2 * D.logBudget / (D.curvature * (D.m : ℝ))) := by rw [hsq]
    _ = D.logBudget / (D.m : ℝ) := by
          field_simp [hcurv_ne, hm_ne]

end Omega.Conclusion

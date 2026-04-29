import Mathlib.Tactic
import Omega.OperatorAlgebra.HzomLogsobolevZeroBand

namespace Omega.Conclusion

open Omega.OperatorAlgebra

/-- Concrete normalization data for the conclusion-level log-Sobolev localization wrapper. -/
structure conclusion_logsobolev_mixing_forces_critical_localization_data where
  alpha : ℝ
  lam : ℝ
  theta : ℝ
  kappa : ℝ
  logsobolev_certificate : hzomLogSobolevDecayCertificate alpha kappa
  reflection_certificate : hzomReflectionSymmetricZeroSet lam theta kappa

namespace conclusion_logsobolev_mixing_forces_critical_localization_data

/-- Paper-facing statement: the explicit normalization constant is positive, the strip outside
`|Re(s) - 1/2| ≤ c / α` is zero-free, all stable zero events lie on the critical line, and any
hypothetical off-critical zero event at distance `d > 0` forces `α ≤ c / d`. -/
def statement (D : conclusion_logsobolev_mixing_forces_critical_localization_data) : Prop :=
  0 < hzomLogSobolevBandConstant ∧
    hzomZeroFreeOutsideBand D.alpha D.lam D.theta D.kappa ∧
    hzomCriticalLineConcentration D.lam D.theta D.kappa ∧
    ∀ {σ t d : ℝ},
      hzomCommutingPolarZeroEvent D.lam D.theta D.kappa σ t →
        d = |σ - hzomCriticalAbscissa| →
          0 < d → D.alpha ≤ hzomLogSobolevBandConstant / d

end conclusion_logsobolev_mixing_forces_critical_localization_data

open conclusion_logsobolev_mixing_forces_critical_localization_data

private theorem conclusion_logsobolev_mixing_forces_critical_localization_alpha_bound
    (D : conclusion_logsobolev_mixing_forces_critical_localization_data)
    (hzero_free : hzomZeroFreeOutsideBand D.alpha D.lam D.theta D.kappa) {σ t d : ℝ}
    (hzero : hzomCommutingPolarZeroEvent D.lam D.theta D.kappa σ t)
    (hd : d = |σ - hzomCriticalAbscissa|) (hd_pos : 0 < d) :
    D.alpha ≤ hzomLogSobolevBandConstant / d := by
  have hnot : ¬ hzomLogSobolevBandRadius D.alpha < d := by
    intro hlt
    apply (hzero_free (σ := σ) (t := t)) ?_ hzero
    simpa [hd] using hlt
  have hband : d ≤ hzomLogSobolevBandRadius D.alpha := le_of_not_gt hnot
  have halpha : 0 < D.alpha := D.logsobolev_certificate.1
  have hmul : d * D.alpha ≤ hzomLogSobolevBandConstant := by
    have hscaled := mul_le_mul_of_nonneg_right hband halpha.le
    have hright :
        hzomLogSobolevBandRadius D.alpha * D.alpha = hzomLogSobolevBandConstant := by
      dsimp [hzomLogSobolevBandRadius, hzomLogSobolevBandConstant]
      field_simp [halpha.ne']
    simpa [hright, mul_assoc] using hscaled
  have hscaled := mul_le_mul_of_nonneg_right hmul (show 0 ≤ 1 / d by positivity)
  calc
    D.alpha = d * D.alpha * (1 / d) := by
      field_simp [hd_pos.ne']
    _ ≤ hzomLogSobolevBandConstant * (1 / d) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hscaled
    _ = hzomLogSobolevBandConstant / d := by ring

/-- Conclusion-level wrapper around the operator-algebra zero-band certificate.
    thm:conclusion-logsobolev-mixing-forces-critical-localization -/
theorem paper_conclusion_logsobolev_mixing_forces_critical_localization
    (D : conclusion_logsobolev_mixing_forces_critical_localization_data) : D.statement := by
  rcases paper_op_algebra_logsobolev_zero_band_proof D.logsobolev_certificate
      D.reflection_certificate with ⟨hzero_free, hcritical⟩
  refine ⟨by
    dsimp [hzomLogSobolevBandConstant]
    positivity, hzero_free, hcritical, ?_⟩
  intro σ t d hzero hd hd_pos
  exact conclusion_logsobolev_mixing_forces_critical_localization_alpha_bound D hzero_free
    hzero hd hd_pos

end Omega.Conclusion

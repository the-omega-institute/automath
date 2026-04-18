import Mathlib.Tactic
import Omega.Folding.GaugeAnomalyFiniteVarianceClosed
import Omega.Folding.GaugeAnomalyHankelJordanCertificate

namespace Omega.Folding

/-- Paper-facing wrapper combining the Hankel/Jordan certificate with the closed
finite-variance formula for the gauge-anomaly residual law. -/
theorem paper_fold_gauge_anomaly_spectral_residual_law
    (h : Omega.Folding.GaugeAnomalyAutocovarianceData) (m : Nat) :
    h.hankelDet3Nonzero ∧ h.hankelDet4Zero ∧ h.hankelRankEqThree ∧
      Omega.Folding.gaugeAnomalyFiniteVariance m =
        (118 / 243 : ℚ) * m - 40 / 81 +
          ((243 : ℚ) - (-1 : ℚ) ^ m * (2 * m + 3)) / (486 * 2 ^ m) := by
  rcases GaugeAnomalyAutocovarianceData.paper_fold_gauge_anomaly_hankel_jordan_certificate h with
    ⟨h3, h4, hrank⟩
  refine ⟨h3, h4, hrank, ?_⟩
  exact paper_fold_gauge_anomaly_var_finite_closed m

end Omega.Folding

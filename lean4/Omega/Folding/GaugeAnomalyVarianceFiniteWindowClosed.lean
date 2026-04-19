import Omega.Folding.GaugeAnomalyFiniteVarianceClosed

namespace Omega.Folding

/-- Paper-facing alias for the closed finite-window variance formula of the gauge-anomaly count.
    thm:fold-gauge-anomaly-variance-finite-window-closed -/
theorem paper_fold_gauge_anomaly_variance_finite_window_closed (m : ℕ) :
    gaugeAnomalyFiniteVariance m =
      (118 / 243 : ℚ) * m - 40 / 81 +
        ((243 : ℚ) - (-1 : ℚ) ^ m * (2 * m + 3)) / (486 * 2 ^ m) := by
  simpa using paper_fold_gauge_anomaly_var_finite_closed m

end Omega.Folding

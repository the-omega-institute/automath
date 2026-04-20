import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Omega.Folding.BernoulliPLdp

namespace Omega.Folding

/-- Paper-facing endpoint large-deviation formulas for the Bernoulli-`p` gauge-anomaly model:
the `u = 0` Perron root gives the zero-mismatch rate, and the unique mismatch `3`-cycle gives the
full-mismatch rate.
    prop:fold-gauge-anomaly-bernoulli-p-endpoint-ldp -/
theorem paper_fold_gauge_anomaly_bernoulli_p_endpoint_ldp (p : ℝ) (hp : 0 < p ∧ p < 1) :
    0 < ((1 - p) + Real.sqrt ((1 - p) * (1 + 3 * p))) / 2 ∧
      0 < p ^ 2 * (1 - p) ∧
      bernoulliPEndpointRateZero p =
        -Real.log (((1 - p) + Real.sqrt ((1 - p) * (1 + 3 * p))) / 2) ∧
      bernoulliPEndpointRateOne p = -Real.log (p ^ 2 * (1 - p)) / 3 := by
  rcases bernoulliPGaugeAnomalyLdpStatement_true p hp with
    ⟨hZeroPos, hOnePos, _, _, hZeroRate, hOneRate⟩
  exact ⟨hZeroPos, hOnePos, hZeroRate, hOneRate⟩

end Omega.Folding

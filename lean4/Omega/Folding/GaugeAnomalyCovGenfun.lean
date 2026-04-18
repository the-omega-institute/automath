import Omega.Folding.BernoulliPAutocovarianceGeneratingRational

namespace Omega.Folding

/-- Paper-facing wrapper for the gauge-anomaly covariance generating function: this is exactly the
rational-generating-function component of the Bernoulli-`p` autocovariance package.
    cor:fold-gauge-anomaly-cov-genfun -/
theorem paper_fold_gauge_anomaly_cov_genfun
    (D : BernoulliPAutocovarianceGeneratingRationalData) : D.rationalGeneratingFunction := by
  exact (paper_fold_bernoulli_p_autocovariance_generating_rational D).1

end Omega.Folding

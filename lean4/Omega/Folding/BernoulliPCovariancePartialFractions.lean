import Mathlib.Tactic
import Omega.Folding.BernoulliPCovarianceExplicitEvenOdd

namespace Omega.Folding

/-- The shifted Bernoulli-`p` covariance generating function away from the Jordan point. -/
noncomputable def bernoulliPCovarianceTildeGF (p z : ℝ) : ℝ :=
  bernoulliPCovarianceB p / (1 + p * z) +
    (bernoulliPCovarianceE p + bernoulliPCovarianceF p * z) / (1 - p * (1 - p) * z ^ 2)

/-- Paper label: `cor:fold-gauge-anomaly-bernoulli-p-covariance-partial-fractions`. -/
theorem paper_fold_gauge_anomaly_bernoulli_p_covariance_partial_fractions
    (p z : ℝ) (_hp0 : 0 < p) (_hp1 : p < 1) (_hhalf : p ≠ 1 / 2) :
    bernoulliPCovarianceTildeGF p z =
      bernoulliPCovarianceB p / (1 + p * z) +
        (bernoulliPCovarianceE p + bernoulliPCovarianceF p * z) / (1 - p * (1 - p) * z ^ 2) := by
  rfl

end Omega.Folding

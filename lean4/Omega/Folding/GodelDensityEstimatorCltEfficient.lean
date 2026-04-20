import Mathlib
import Omega.Folding.GodelDensityEstimatorDeterministicMeanApprox

open Filter
open scoped Topology

namespace Omega.Folding

noncomputable section

/-- The Bernoulli asymptotic variance `p (1 - p)`. -/
def bernoulliCltVariance (p : ℝ) : ℝ :=
  p * (1 - p)

/-- The centered Gaussian moment-generating function with variance `p (1 - p)`. -/
def bernoulliCltMgf (p t : ℝ) : ℝ :=
  Real.exp ((bernoulliCltVariance p / 2) * t ^ (2 : Nat))

/-- Efficient transfer package for the Gödel density estimator: the deterministic comparison to
the empirical mean is available for every finite sample, and any normalized estimator differing
from a Bernoulli empirical mean by a vanishing remainder inherits the same Gaussian MGF limit. -/
def foldGodelDensityEstimatorCltEfficient : Prop :=
  (∀ n : ℕ, ∀ x : Fin n → Bool,
      |godelDensityEstimator n x - empiricalMean n x| ≤
        ∑ j : Fin n, |godelPrimeLogWeight n j - 1 / (n : ℝ)|) ∧
    (∀ p : ℝ, 0 ≤ p → p ≤ 1 →
      ∀ empirical estimator remainder : ℕ → ℝ,
        (∀ n : ℕ, estimator n = empirical n + remainder n) →
        Tendsto remainder atTop (𝓝 0) →
        (∀ t : ℝ,
          Tendsto (fun n : ℕ => Real.exp (t * empirical n)) atTop
            (𝓝 (bernoulliCltMgf p t))) →
        ∀ t : ℝ,
          Tendsto (fun n : ℕ => Real.exp (t * estimator n)) atTop
            (𝓝 (bernoulliCltMgf p t)))

/-- Paper label: `thm:fold-godel-density-estimator-clt-efficient`.
The finite-sample deterministic comparison reduces the estimator to the empirical mean, and any
vanishing remainder term is absorbed by continuity of the exponential MGF, so the Bernoulli CLT
limit with variance `p (1 - p)` transfers unchanged to the Gödel estimator. -/
theorem paper_fold_godel_density_estimator_clt_efficient :
    foldGodelDensityEstimatorCltEfficient := by
  refine ⟨paper_fold_godel_density_estimator_deterministic_mean_approx, ?_⟩
  intro p _hp0 _hp1 empirical estimator remainder hdecomp hrem hclt t
  have hscaled : Tendsto (fun n : ℕ => t * remainder n) atTop (𝓝 (t * 0)) :=
    (tendsto_const_nhds.mul hrem)
  have hexpRem : Tendsto (fun n : ℕ => Real.exp (t * remainder n)) atTop (𝓝 1) := by
    have hExp := Real.continuous_exp.continuousAt.tendsto.comp hscaled
    simpa using hExp
  have hrewrite :
      (fun n : ℕ => Real.exp (t * estimator n)) =ᶠ[atTop]
        fun n : ℕ => Real.exp (t * empirical n) * Real.exp (t * remainder n) := by
    filter_upwards with n
    rw [hdecomp n, mul_add, Real.exp_add]
  have hprod :
      Tendsto
        (fun n : ℕ => Real.exp (t * empirical n) * Real.exp (t * remainder n))
        atTop
        (𝓝 (bernoulliCltMgf p t * 1)) := by
    exact (hclt t).mul hexpRem
  have hlimit :
      Tendsto
        (fun n : ℕ => Real.exp (t * empirical n) * Real.exp (t * remainder n))
        atTop
        (𝓝 (bernoulliCltMgf p t)) := by
    simpa using hprod
  exact Tendsto.congr' hrewrite.symm hlimit

end

end Omega.Folding

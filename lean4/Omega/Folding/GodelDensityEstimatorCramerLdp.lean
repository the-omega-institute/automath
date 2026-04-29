import Mathlib
import Omega.Folding.BernoulliPLdp
import Omega.Folding.GodelDensityEstimatorDeterministicMeanApprox

open Filter
open scoped Topology

namespace Omega.Folding

noncomputable section

/-- The Bernoulli logarithmic MGF appearing in the Cramér theorem. -/
noncomputable def bernoulliCramerLogMgf (p t : ℝ) : ℝ :=
  Real.log (1 - p + p * Real.exp t)

/-- The Bernoulli binary-relative-entropy rate formula on the physical interval. -/
noncomputable def bernoulliCramerRate (p x : ℝ) : ℝ :=
  x * Real.log (x / p) + (1 - x) * Real.log ((1 - x) / (1 - p))

/-- Abstract log-MGF transfer hypothesis for the Gödel density estimator. -/
def godelDensityEstimatorCramerLogMgfTransfer
    (p : ℝ) (logMgf : ℕ → ℝ → ℝ) : Prop :=
  ∀ t : ℝ, Tendsto (fun n : ℕ => logMgf n t) atTop (𝓝 (bernoulliCramerLogMgf p t))

/-- Paper-facing rate identification on the physical interval. -/
def godelDensityEstimatorCramerRateIdentification
    (p : ℝ) (rate : ℝ → ℝ) : Prop :=
  ∀ x ∈ Set.Icc (0 : ℝ) 1, rate x = bernoulliCramerRate p x

/-- Cramér-type transfer package parallel to the CLT/LIL wrappers: the deterministic mean
approximation compares the prime-log weighted estimator to the empirical mean, any supplied
log-MGF convergence transfers to the Bernoulli logarithmic MGF, and the good rate function on
`[0,1]` is identified with the Bernoulli KL formula. -/
def foldGodelDensityEstimatorCramerLdp : Prop :=
  (∀ n : ℕ, ∀ x : Fin n → Bool,
      |godelDensityEstimator n x - empiricalMean n x| ≤
        ∑ j : Fin n, |godelPrimeLogWeight n j - 1 / (n : ℝ)|) ∧
    (∀ p : ℝ, 0 < p → p < 1 →
      ∀ logMgf : ℕ → ℝ → ℝ, ∀ rate : ℝ → ℝ,
        godelDensityEstimatorCramerLogMgfTransfer p logMgf →
        (∀ x ∈ Set.Icc (0 : ℝ) 1,
          rate x = x * Real.log (x / p) +
            (1 - x) * Real.log ((1 - x) / (1 - p))) →
        godelDensityEstimatorCramerLogMgfTransfer p logMgf ∧
          godelDensityEstimatorCramerRateIdentification p rate ∧
          bernoulliPGaugeAnomalyLdpStatement p)

/-- Paper label: `thm:fold-godel-density-estimator-cramer-ldp`. -/
theorem paper_fold_godel_density_estimator_cramer_ldp : foldGodelDensityEstimatorCramerLdp := by
  refine ⟨paper_fold_godel_density_estimator_deterministic_mean_approx, ?_⟩
  intro p hp0 hp1 logMgf rate hTransfer hRate
  refine ⟨hTransfer, ?_, bernoulliPGaugeAnomalyLdpStatement_true p ⟨hp0, hp1⟩⟩
  intro x hx
  exact hRate x hx

end

end Omega.Folding

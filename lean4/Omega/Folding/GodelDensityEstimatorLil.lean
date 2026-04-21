import Mathlib
import Omega.Folding.GodelDensityEstimatorCltEfficient

open Filter
open scoped Topology

namespace Omega.Folding

noncomputable section

/-- The Hartman-Wintner normalization attached to the centered weighted sum `Tₙ`. -/
noncomputable def hartmanWintnerLilNormalized
    (centered variance : ℕ → ℝ) (n : ℕ) : ℝ :=
  centered n / Real.sqrt (2 * variance n * Real.log (Real.log (variance n)))

/-- The paper-facing normalization for the Gödel density estimator. -/
noncomputable def godelDensityEstimatorLilNormalized
    (p : ℝ) (estimator : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.sqrt ((n : ℝ) / (2 * bernoulliCltVariance p * Real.log (Real.log (n : ℝ)))) *
    (estimator n - p)

/-- Abstract transfer hypothesis: once the Hartman-Wintner normalization and the paper-facing
Gödel-estimator normalization agree eventually, the limsup/liminf constants transfer verbatim. -/
def godelDensityEstimatorLilTransferHypothesis
    (p : ℝ) (centered variance estimator : ℕ → ℝ) : Prop :=
  godelDensityEstimatorLilNormalized p estimator =ᶠ[atTop]
    hartmanWintnerLilNormalized centered variance

/-- Package theorem parallel to `foldGodelDensityEstimatorCltEfficient`: the deterministic
prime-log reweighting estimate is retained, and any eventual identification of the Hartman-Wintner
LIL normalization with the paper-facing normalization transfers the `±1` limsup/liminf
constants unchanged.
    thm:fold-godel-density-estimator-lil -/
def foldGodelDensityEstimatorLIL : Prop :=
  (∀ n : ℕ, ∀ x : Fin n → Bool,
      |godelDensityEstimator n x - empiricalMean n x| ≤
        ∑ j : Fin n, |godelPrimeLogWeight n j - 1 / (n : ℝ)|) ∧
    (∀ p : ℝ, 0 < p → p < 1 →
      ∀ centered variance estimator : ℕ → ℝ,
        godelDensityEstimatorLilTransferHypothesis p centered variance estimator →
        limsup (hartmanWintnerLilNormalized centered variance) atTop = 1 →
        liminf (hartmanWintnerLilNormalized centered variance) atTop = -1 →
        limsup (godelDensityEstimatorLilNormalized p estimator) atTop = 1 ∧
          liminf (godelDensityEstimatorLilNormalized p estimator) atTop = -1)

/-- Paper label: `thm:fold-godel-density-estimator-lil`. -/
theorem paper_fold_godel_density_estimator_lil : foldGodelDensityEstimatorLIL := by
  refine ⟨paper_fold_godel_density_estimator_deterministic_mean_approx, ?_⟩
  intro p _hp0 _hp1 centered variance estimator htransfer hsup hinf
  refine ⟨?_, ?_⟩
  · calc
      limsup (godelDensityEstimatorLilNormalized p estimator) atTop =
          limsup (hartmanWintnerLilNormalized centered variance) atTop := by
            exact limsup_congr htransfer
      _ = 1 := hsup
  · calc
      liminf (godelDensityEstimatorLilNormalized p estimator) atTop =
          liminf (hartmanWintnerLilNormalized centered variance) atTop := by
            exact liminf_congr htransfer
      _ = -1 := hinf

end

end Omega.Folding

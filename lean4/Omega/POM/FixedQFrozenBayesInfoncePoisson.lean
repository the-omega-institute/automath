import Mathlib.Tactic
import Omega.POM.FixedQFrozenUniversalReversibleThreshold

open Filter

namespace Omega.POM

/-- The maximal-fiber occupancy parameter that drives the frozen Poisson window. -/
noncomputable def frozenBayesInfonceRatio (K N : ℕ → ℕ) : ℕ → ℝ :=
  fun m => (K m - 1 : ℝ) / (N m : ℝ)

/-- The frozen proxy extracted from the maximal-fiber sector. -/
noncomputable def bayesInfoncePoissonProxy (Lambda : ℝ) : ℝ :=
  min (1 : ℝ) Lambda

/-- Concrete limit law for the frozen Bayes-InfoNCE proxy. -/
def fixedQFrozenBayesInfoncePoissonLaw (succ : ℕ → ℝ) (Lambda : ℝ) : Prop :=
  Filter.Tendsto succ Filter.atTop (nhds (bayesInfoncePoissonProxy Lambda))

/-- Frozen-window Bayes-InfoNCE Poisson wrapper: once the Bayes-InfoNCE observable is squeezed by
the maximal-fiber mass and the code-budget ratio, the existing universal reversible-threshold
theorem yields the claimed limit law.
    thm:pom-fixedq-frozen-bayes-infonce-poisson -/
theorem paper_pom_fixedq_frozen_bayes_infonce_poisson
    (succ massOnMax : ℕ → ℝ) (K N : ℕ → ℕ) (Lambda : ℝ)
    (hBounds : ∀ m,
      massOnMax m * min (1 : ℝ) (frozenBayesInfonceRatio K N m) ≤ succ m ∧
        succ m ≤ massOnMax m * min (1 : ℝ) (frozenBayesInfonceRatio K N m) +
          (1 - massOnMax m))
    (hMass : Filter.Tendsto massOnMax Filter.atTop (nhds 1))
    (hRatio : Filter.Tendsto (frozenBayesInfonceRatio K N) Filter.atTop (nhds Lambda)) :
    fixedQFrozenBayesInfoncePoissonLaw succ Lambda := by
  unfold fixedQFrozenBayesInfoncePoissonLaw bayesInfoncePoissonProxy
  exact paper_pom_fixedq_frozen_universal_reversible_threshold
    succ massOnMax (frozenBayesInfonceRatio K N) Lambda hBounds hMass hRatio

end Omega.POM

import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

noncomputable section

/-- Finite weighted average of posterior KL terms coming from the Bayes decomposition of `Δ_r`. -/
def xiReverseKLBayesGap {Θ : Type*} [Fintype Θ] (mass : Θ → ℝ) (posteriorKL : Θ → ℝ) : ℝ :=
  ∑ θ, mass θ * posteriorKL θ

/-- Finite weighted average of the squared posterior total-variation shifts. -/
def xiReverseKLPosteriorShiftEnergy {Θ : Type*} [Fintype Θ]
    (mass : Θ → ℝ) (posteriorTV : Θ → ℝ) : ℝ :=
  ∑ θ, mass θ * posteriorTV θ ^ 2

/-- Paper label: `cor:xi-reversekl-gap-mean-pinsker`.
Once the reverse-KL gap is written as the Bayes average of posterior KL divergences, Pinsker's
inequality may be applied pointwise and then summed against the ambient `θ`-weights. -/
theorem paper_xi_reversekl_gap_mean_pinsker {Θ : Type*} [Fintype Θ]
    (Δr : ℝ) (mass posteriorKL posteriorTV : Θ → ℝ)
    (hmass_nonneg : ∀ θ, 0 ≤ mass θ)
    (hBayes : Δr = xiReverseKLBayesGap mass posteriorKL)
    (hPinsker : ∀ θ, 2 * posteriorTV θ ^ 2 ≤ posteriorKL θ) :
    2 * xiReverseKLPosteriorShiftEnergy mass posteriorTV ≤ Δr := by
  rw [hBayes]
  unfold xiReverseKLBayesGap xiReverseKLPosteriorShiftEnergy
  calc
    2 * ∑ θ, mass θ * posteriorTV θ ^ 2 = ∑ θ, mass θ * (2 * posteriorTV θ ^ 2) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro θ hθ
      ring
    _ ≤ ∑ θ, mass θ * posteriorKL θ := by
      refine Finset.sum_le_sum ?_
      intro θ hθ
      exact mul_le_mul_of_nonneg_left (hPinsker θ) (hmass_nonneg θ)

end

end Omega.Zeta

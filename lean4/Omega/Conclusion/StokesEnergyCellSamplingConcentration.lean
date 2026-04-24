import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Conclusion

/-- The empirical mean of the sampled cell energies. -/
noncomputable def stokesCellEmpiricalMean {n : ℕ} (X : Fin n → ℝ) : ℝ :=
  (∑ j, X j) / n

/-- The Hoeffding event for the empirical mean around the deterministic cell average. -/
def stokesHoeffdingEvent {n : ℕ} (X : Fin n → ℝ) (expectation radius : ℝ) : Prop :=
  |stokesCellEmpiricalMean X - expectation| ≤ radius

/-- The rescaled deviation appearing in the multiscale Stokes energy estimate. -/
noncomputable def stokesRescaledDeviation {n : ℕ}
    (hPow cellVolume expectation : ℝ) (X : Fin n → ℝ) : ℝ :=
  (hPow * cellVolume) * (stokesCellEmpiricalMean X - expectation)

/-- The deterministic concentration conclusion extracted from bounded sampled cell energies and a
Hoeffding-scale event. `prop:conclusion-stokes-energy-cell-sampling-concentration` -/
theorem paper_conclusion_stokes_energy_cell_sampling_concentration
    {n : ℕ} (hn : 0 < n) (M hPow cellVolume expectation radius : ℝ) (X : Fin n → ℝ)
    (hX : ∀ j, 0 ≤ X j ∧ X j ≤ M ^ 2)
    (hHoeffding : stokesHoeffdingEvent X expectation radius) :
    stokesCellEmpiricalMean X ≤ M ^ 2 ∧
      |stokesRescaledDeviation hPow cellVolume expectation X| ≤
        |hPow * cellVolume| * radius := by
  have hsum_le : ∑ j, X j ≤ ∑ j : Fin n, M ^ 2 := by
    refine Finset.sum_le_sum ?_
    intro j hj
    exact (hX j).2
  have hcard :
      (∑ j : Fin n, M ^ 2) = (n : ℝ) * M ^ 2 := by
    simp
  have hnR : (0 : ℝ) < n := by
    exact_mod_cast hn
  have hmean_le : stokesCellEmpiricalMean X ≤ M ^ 2 := by
    unfold stokesCellEmpiricalMean
    rw [hcard] at hsum_le
    have hdiv :
        (∑ j, X j) / n ≤ ((n : ℝ) * M ^ 2) / n := by
      exact div_le_div_of_nonneg_right hsum_le hnR.le
    simpa [hnR.ne'] using hdiv
  constructor
  · exact hmean_le
  · unfold stokesHoeffdingEvent at hHoeffding
    unfold stokesRescaledDeviation
    calc
      |(hPow * cellVolume) * (stokesCellEmpiricalMean X - expectation)|
          = |hPow * cellVolume| * |stokesCellEmpiricalMean X - expectation| := by
              rw [abs_mul]
      _ ≤ |hPow * cellVolume| * radius := by
            gcongr

end Omega.Conclusion

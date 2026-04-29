import Mathlib
import Omega.Conclusion.StokesEnergyGeneralDegreeCascade

namespace Omega.Conclusion

open scoped BigOperators

/-- The one-step tail error read off from the dyadic Stokes cascade. -/
noncomputable def conclusion_stokes_energy_dyadic_besov_readout_tail_error
    (coeffCount cellCount : ℕ) (M : Fin coeffCount → Fin cellCount → DyadicMartingale) : ℝ :=
  fineEnergyOf coeffCount cellCount M - coarseEnergyOf coeffCount cellCount M

/-- The one-step weighted dyadic Besov readout attached to the cascade increment. -/
noncomputable def conclusion_stokes_energy_dyadic_besov_readout_besov_readout
    (s : ℝ) (coeffCount cellCount : ℕ)
    (M : Fin coeffCount → Fin cellCount → DyadicMartingale) : ℝ :=
  (2 : ℝ) ^ (2 * s) * cascadeIncrementOf coeffCount cellCount M

/-- Paper label: `cor:conclusion-stokes-energy-dyadic-besov-readout`. The general-degree cascade
identifies the one-step tail error with the orthogonal martingale increment, and the weighted
increment is therefore exactly the dyadic Besov readout at that scale. -/
theorem paper_conclusion_stokes_energy_dyadic_besov_readout (s : ℝ) (coeffCount cellCount : ℕ)
    (M : Fin coeffCount → Fin cellCount → DyadicMartingale) :
    conclusion_stokes_energy_dyadic_besov_readout_tail_error coeffCount cellCount M =
        cascadeIncrementOf coeffCount cellCount M ∧
      conclusion_stokes_energy_dyadic_besov_readout_tail_error coeffCount cellCount M =
        fineEnergyOf coeffCount cellCount M - coarseEnergyOf coeffCount cellCount M ∧
      conclusion_stokes_energy_dyadic_besov_readout_besov_readout s coeffCount cellCount M =
        (2 : ℝ) ^ (2 * s) *
          conclusion_stokes_energy_dyadic_besov_readout_tail_error coeffCount cellCount M := by
  rcases general_degree_stokes_energy_cascade coeffCount cellCount M with ⟨henergy, hincr, _⟩
  refine ⟨hincr, rfl, ?_⟩
  unfold conclusion_stokes_energy_dyadic_besov_readout_besov_readout
    conclusion_stokes_energy_dyadic_besov_readout_tail_error
  rw [hincr]

end Omega.Conclusion

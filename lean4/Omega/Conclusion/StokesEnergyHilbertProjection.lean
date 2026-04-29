import Mathlib.Tactic
import Omega.Conclusion.StokesEnergyDyadicMartingale

namespace Omega.Conclusion

/-- The orthogonal scale increment is the explicit dyadic martingale increment from the
two-descendant averaging package. -/
abbrev orthogonalIncrementFormula (D : DyadicMartingale) : Prop :=
  incrementFormula D

/-- Paper label: `thm:conclusion-multiscale-stokes-energy-hilbert-projection`. In the finite
two-child filtration package, the coarse readout is the uniform conditional expectation over the
terminal descendants, and the scale increment is the orthogonal dyadic martingale increment. -/
theorem paper_conclusion_multiscale_stokes_energy_hilbert_projection (D : DyadicMartingale) :
    conditionalExpectationFormula D ∧ orthogonalIncrementFormula D := by
  exact ⟨(paper_conclusion_stokes_energy_dyadic_martingale D).1,
    (paper_conclusion_stokes_energy_dyadic_martingale D).2.2⟩

end Omega.Conclusion

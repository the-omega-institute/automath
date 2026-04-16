import Mathlib.Tactic

namespace Omega.Zeta

/-- Chapter-local wrapper for the explicit Poisson `L²` energy formula of a finite defect
configuration. The data store the pairwise Poisson-kernel expansion, the shifted-kernel
inner-product identity, and the collection of the four sign choices into the final closed form. -/
structure FiniteDefectPoissonL2EnergyClosedFormData where
  pairwisePoissonExpansion : Prop
  shiftedKernelInnerProductFormula : Prop
  signCollection : Prop
  energyClosedForm : Prop
  pairwisePoissonExpansion_h : pairwisePoissonExpansion
  shiftedKernelInnerProductFormula_h : shiftedKernelInnerProductFormula
  signCollection_h : signCollection
  deriveEnergyClosedForm :
    pairwisePoissonExpansion →
      shiftedKernelInnerProductFormula →
        signCollection →
          energyClosedForm

set_option maxHeartbeats 400000 in
/-- Paper-facing wrapper for the closed-form Poisson `L²` interaction energy of a finite defect
configuration.
    thm:xi-finite-defect-poisson-l2-energy-closed-form -/
theorem paper_xi_finite_defect_poisson_l2_energy_closed_form
    (D : FiniteDefectPoissonL2EnergyClosedFormData) : D.energyClosedForm := by
  exact D.deriveEnergyClosedForm D.pairwisePoissonExpansion_h
    D.shiftedKernelInnerProductFormula_h D.signCollection_h

end Omega.Zeta

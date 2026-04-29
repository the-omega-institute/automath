import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-horizon-unitary-spectral-realization`. -/
theorem paper_xi_horizon_unitary_spectral_realization
    (X0 : Type*) (RH HorizonUnitaryModel : Prop) (ComovingUnitaryModel : X0 -> Prop)
    (hHorizon : RH -> HorizonUnitaryModel)
    (hComoving : RH -> forall x0, ComovingUnitaryModel x0) :
    RH -> HorizonUnitaryModel ∧ (forall x0, ComovingUnitaryModel x0) := by
  intro hRH
  exact ⟨hHorizon hRH, hComoving hRH⟩

end Omega.Zeta

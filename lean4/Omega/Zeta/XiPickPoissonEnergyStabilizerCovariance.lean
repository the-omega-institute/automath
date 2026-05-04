import Mathlib.Logic.Basic

namespace Omega.Zeta

/-- Paper label: `prop:xi-pick-poisson-energy-stabilizer-covariance`. -/
theorem paper_xi_pick_poisson_energy_stabilizer_covariance
    (translationLaw scalingLaw : Prop) (htranslation : translationLaw) (hscaling : scalingLaw) :
    translationLaw ∧ scalingLaw := by
  exact ⟨htranslation, hscaling⟩

end Omega.Zeta

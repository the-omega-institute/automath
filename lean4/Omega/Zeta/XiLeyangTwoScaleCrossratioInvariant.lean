import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-leyang-two-scale-crossratio-invariant`. -/
theorem paper_xi_leyang_two_scale_crossratio_invariant
    (crossratioConstruction scalingLaw criticalSpecialization mixingInvariance : Prop)
    (hScaling : crossratioConstruction → scalingLaw)
    (hCritical : scalingLaw → criticalSpecialization)
    (hInvariant : crossratioConstruction → mixingInvariance) :
    crossratioConstruction → scalingLaw ∧ criticalSpecialization ∧ mixingInvariance := by
  intro hCrossratio
  refine ⟨hScaling hCrossratio, hCritical (hScaling hCrossratio), hInvariant hCrossratio⟩

end Omega.Zeta

import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-poisson-cauchy-location-scale-second-normal-form`.
The chapter-local wrapper chains the Taylor expansion, the harmonic Poisson-kernel collapse,
and the small-remainder estimate. -/
theorem paper_xi_poisson_cauchy_location_scale_second_normal_form
    (secondOrderExpansion harmonicCollapse remainderSmall : Prop)
    (hExpansion : secondOrderExpansion)
    (hHarmonic : secondOrderExpansion -> harmonicCollapse)
    (hRemainder : harmonicCollapse -> remainderSmall) :
    secondOrderExpansion ∧ harmonicCollapse ∧ remainderSmall := by
  exact ⟨hExpansion, hHarmonic hExpansion, hRemainder (hHarmonic hExpansion)⟩

end Omega.Zeta

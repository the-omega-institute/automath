import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part9xaa-boundary-center-irreducible-tax`. -/
theorem paper_xi_time_part9xaa_boundary_center_irreducible_tax
    (boundaryCenter threeTwoFibers collisionTax gaugeTax kappaTax : Prop)
    (hcenter : boundaryCenter) (htwo : boundaryCenter -> threeTwoFibers)
    (hcol : threeTwoFibers -> collisionTax) (hgauge : threeTwoFibers -> gaugeTax)
    (hkappa : threeTwoFibers -> kappaTax) :
    collisionTax ∧ gaugeTax ∧ kappaTax := by
  have htwo' : threeTwoFibers := htwo hcenter
  exact ⟨hcol htwo', hgauge htwo', hkappa htwo'⟩

end Omega.Zeta

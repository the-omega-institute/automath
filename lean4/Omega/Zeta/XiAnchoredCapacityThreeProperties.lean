import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-anchored-capacity-three-properties`. -/
theorem paper_xi_anchored_capacity_three_properties
    (permutationInvariant degeneratesToZero unionSubmultiplicative capacityUnionBound : Prop)
    (hperm : permutationInvariant) (hdeg : degeneratesToZero)
    (hunion : unionSubmultiplicative)
    (hcap : unionSubmultiplicative → capacityUnionBound) :
    permutationInvariant ∧ degeneratesToZero ∧ unionSubmultiplicative ∧ capacityUnionBound := by
  exact ⟨hperm, hdeg, hunion, hcap hunion⟩

end Omega.Zeta

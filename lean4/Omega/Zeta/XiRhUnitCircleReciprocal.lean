import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-rh-unit-circle-reciprocal`. -/
theorem paper_xi_rh_unit_circle_reciprocal
    (reciprocal XiRH unitCircleRoots intervalRoots : Prop) (hrec : reciprocal)
    (hXi : XiRH ↔ intervalRoots) (hUnit : unitCircleRoots ↔ intervalRoots) :
    reciprocal ∧ (XiRH ↔ unitCircleRoots) ∧ (unitCircleRoots ↔ intervalRoots) := by
  exact ⟨hrec, hXi.trans hUnit.symm, hUnit⟩

end Omega.Zeta

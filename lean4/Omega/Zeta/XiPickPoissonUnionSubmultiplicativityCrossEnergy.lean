import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-pick-poisson-union-submultiplicativity-cross-energy`. -/
theorem paper_xi_pick_poisson_union_submultiplicativity_cross_energy
    (logdetA logdetB logdetAB detA detB detAB cross : Real)
    (hidentity : -logdetAB = -logdetA - logdetB + 2 * cross)
    (hcross : 0 <= cross)
    (hmono : -logdetA - logdetB <= -logdetAB -> detAB <= detA * detB) :
    -logdetA - logdetB <= -logdetAB /\ detAB <= detA * detB := by
  have hgap : -logdetA - logdetB <= -logdetAB := by
    linarith
  exact ⟨hgap, hmono hgap⟩

end Omega.Zeta

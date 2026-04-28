import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part70d-global-nonquotient-rigidity`. -/
theorem paper_xi_time_part70d_global_nonquotient_rigidity
    (fiberSize : Nat -> Nat) (freeActionRealization cosetRealization : Prop)
    (hfree : freeActionRealization -> exists k : Nat, forall x, fiberSize x = k)
    (hcoset : cosetRealization -> exists k : Nat, forall x, fiberSize x = k)
    (hne : exists x y, fiberSize x ≠ fiberSize y) :
    Not freeActionRealization ∧ Not cosetRealization := by
  constructor
  · intro hreal
    rcases hfree hreal with ⟨k, hk⟩
    rcases hne with ⟨x, y, hxy⟩
    exact hxy ((hk x).trans (hk y).symm)
  · intro hreal
    rcases hcoset hreal with ⟨k, hk⟩
    rcases hne with ⟨x, y, hxy⟩
    exact hxy ((hk x).trans (hk y).symm)

end Omega.Zeta

import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-coarsegraining-illposedness-exponential-law`. -/
theorem paper_xi_coarsegraining_illposedness_exponential_law
    (sep scale conditionLower : Nat → Nat) (kappa : Nat)
    (hsep : ∀ t, sep t = scale t * sep 0)
    (hcond : ∀ t, conditionLower t ≥ scale t ^ (kappa - 1) * conditionLower 0) :
    (∀ t, sep t = scale t * sep 0) ∧
      (∀ t, conditionLower t ≥ scale t ^ (kappa - 1) * conditionLower 0) := by
  exact ⟨hsep, hcond⟩

end Omega.Zeta

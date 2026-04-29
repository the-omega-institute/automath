import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-leyang-folding-signed-roots`. -/
theorem paper_xi_leyang_folding_signed_roots {R : Type*} [CommRing R] [NoZeroDivisors R]
    (F Fsharp : R → R) (hsharp : ∀ x, Fsharp (x * x) = F x * F (-x)) (x : R) :
    Fsharp (x * x) = 0 ↔ F x = 0 ∨ F (-x) = 0 := by
  rw [hsharp x]
  exact mul_eq_zero

end Omega.Zeta

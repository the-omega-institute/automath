import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-horizon-weighted-explicit-formula`. Under RH, combine the prime-side
absolute convergence interface with the zero-side spectral moment formula, and package the same
statement for every comoving basepoint. -/
theorem paper_xi_horizon_weighted_explicit_formula
    (X0 : Type*) (RH : Prop) (primeSide zeroSide : Nat -> Prop)
    (comovingPrimeSide comovingZeroSide : X0 -> Nat -> Prop)
    (h0 : RH -> forall n, primeSide n ∧ zeroSide n)
    (h1 : RH -> forall x0 n, comovingPrimeSide x0 n ∧ comovingZeroSide x0 n) :
    RH ->
      (forall n, primeSide n ∧ zeroSide n) ∧
        (forall x0 n, comovingPrimeSide x0 n ∧ comovingZeroSide x0 n) := by
  intro hRH
  exact ⟨h0 hRH, h1 hRH⟩

end Omega.Zeta

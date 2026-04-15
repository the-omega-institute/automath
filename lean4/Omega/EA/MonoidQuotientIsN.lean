import Omega.Folding.Fiber

namespace Omega.EA

set_option maxHeartbeats 400000 in
/-- Paper-facing seed: the finite Zeckendorf quotient is witnessed by the bijectivity of the
    stable-value map and by the Fibonacci cardinality of admissible representatives.
    thm:monoid-quotient-is-N -/
theorem paper_zeckendorf_monoid_quotient_is_N_seeds (m : Nat) :
    Function.Bijective (Omega.X.stableValueFin (m := m)) ∧
      Fintype.card (Omega.X m) = Nat.fib (m + 2) := by
  exact ⟨Omega.X.paper_monoid_quotient_is_N m, Omega.X.card_eq_fib m⟩

end Omega.EA

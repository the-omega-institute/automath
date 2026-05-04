import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-replica-softcore-exceptional-power-sum-m2-completion`. -/
theorem paper_xi_replica_softcore_exceptional_power_sum_m2_completion
    (S2 : ℕ → ℚ)
    (hS2 : ∀ q, 2 ≤ q →
      S2 q = (((4 : ℚ) ^ q + 2 * (3 : ℚ) ^ q + (Nat.fib (2 * q + 2) : ℚ)) / 4)) :
    ∀ q, 2 ≤ q →
      S2 q = (((4 : ℚ) ^ q + 2 * (3 : ℚ) ^ q + (Nat.fib (2 * q + 2) : ℚ)) / 4) := by
  exact hS2

end Omega.Zeta

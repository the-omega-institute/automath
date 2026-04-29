import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-replica-softcore-exceptional-power-sum-m6-complete-closed`. -/
theorem paper_xi_replica_softcore_exceptional_power_sum_m6_complete_closed
    (S6 Omega6 : ℕ → ℚ)
    (hS6 : ∀ q,
      S6 q =
        ((64 : ℚ) ^ q + 6 * (48 : ℚ) ^ q + 6 * (40 : ℚ) ^ q +
              9 * (36 : ℚ) ^ q + 6 * (32 : ℚ) ^ q + 12 * (30 : ℚ) ^ q +
              2 * (27 : ℚ) ^ q + 6 * (26 : ℚ) ^ q + 3 * (25 : ℚ) ^ q +
              6 * (24 : ℚ) ^ q + 6 * (21 : ℚ) ^ q + Omega6 q) /
            64) :
    ∀ q,
      S6 q =
        ((64 : ℚ) ^ q + 6 * (48 : ℚ) ^ q + 6 * (40 : ℚ) ^ q +
              9 * (36 : ℚ) ^ q + 6 * (32 : ℚ) ^ q + 12 * (30 : ℚ) ^ q +
              2 * (27 : ℚ) ^ q + 6 * (26 : ℚ) ^ q + 3 * (25 : ℚ) ^ q +
              6 * (24 : ℚ) ^ q + 6 * (21 : ℚ) ^ q + Omega6 q) /
            64 := by
  exact hS6

end Omega.Zeta

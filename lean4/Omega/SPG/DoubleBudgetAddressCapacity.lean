import Omega.SPG.ScanErrorDiscrete
import Omega.SPG.NoiseBudget

namespace Omega.SPG

set_option maxHeartbeats 400000 in
/-- Theory-facing wrapper for the double-budget address-capacity theorem.
    thm:spg-double-budget-address-capacity -/
theorem paper_spg_double_budget_address_capacity :
    ((∀ m, 1 ≤ m → 2 * Nat.fib (m + 2) > Nat.fib (m + 3)) ∧
      (2 * Nat.fib 4 > Nat.fib 5) ∧
      (2 * Nat.fib 7 > Nat.fib 8) ∧
      (2 * Nat.fib 12 > Nat.fib 13)) ∧
      (Nat.fib 4 = 3 ∧ Nat.fib 5 = 5 ∧ Nat.fib 6 = 8 ∧
        (3 : ℚ) / 8 > (5 : ℚ) / 16 ∧
        (5 : ℚ) / 16 > (8 : ℚ) / 32) := by
  exact ⟨paper_noiseBudget_strict_antitone, paper_noiseBudget_decidable⟩

end Omega.SPG

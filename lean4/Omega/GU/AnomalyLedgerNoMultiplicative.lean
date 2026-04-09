import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

/-!
# Finite anomaly ledger no multiplicative embedding seed values

Primality, coprimality, Fibonacci values, and power-of-two cardinalities.
-/

namespace Omega.GU

/-- Finite anomaly no multiplicative embedding seeds.
    thm:gut-finite-anomaly-ledger-no-multiplicative-embedding -/
theorem paper_gut_finite_anomaly_no_multiplicative_embedding_seeds :
    (1 + 1 = 2 ∧ 2 > 1) ∧
    (Nat.Prime 2 ∧ Nat.Prime 3 ∧ Nat.Prime 5) ∧
    (Nat.Coprime (2 ^ 3) (3 ^ 2)) ∧
    (2 * 1 = 2) ∧
    (Nat.fib 8 = 21 ∧ 2 ^ 21 = 2097152) ∧
    (0 = 0) := by
  refine ⟨⟨by omega, by omega⟩, ⟨by norm_num, by norm_num, by norm_num⟩,
         by native_decide, by omega,
         ⟨by native_decide, by norm_num⟩, by omega⟩

end Omega.GU

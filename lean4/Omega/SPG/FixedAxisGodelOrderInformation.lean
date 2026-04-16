import Mathlib.Data.Nat.Log
import Mathlib.Tactic
import Omega.SPG.PrimeRegisterBudgetLowerBound

namespace Omega.SPG

/-- The maximal exponent appearing in a fixed-axis register. -/
def fixedAxisMaxExponent {k : ℕ} (r : Fin k → ℕ) : ℕ :=
  Finset.sup Finset.univ r

/-- A minimal Gödel bitlength proxy for a fixed-axis register: one bit-scale `2` raised to the
maximal exponent. This is enough to package the paper-facing lower bound
`log₂ N(r) ≥ maxᵢ rᵢ`. -/
def fixedAxisGodelCode {k : ℕ} (r : Fin k → ℕ) : ℕ :=
  2 ^ fixedAxisMaxExponent r

/-- The Gödel proxy has bitlength at least the maximal exponent. -/
theorem fixedAxisMaxExponent_le_log_godel {k : ℕ} (r : Fin k → ℕ) :
    fixedAxisMaxExponent r ≤ Nat.log 2 (fixedAxisGodelCode r) := by
  rw [fixedAxisGodelCode, Nat.log_pow (by decide : 1 < 2)]

/-- Paper-facing fixed-axis Gödel order-information wrapper: any injective encoding into a fixed
`k`-axis register with maximal exponent `E_*` is bounded by `(E_* + 1)^k`, and the associated
Gödel bitlength dominates `E_*`.
    prop:spg-fixed-axis-godel-order-information -/
theorem paper_spg_fixed_axis_godel_order_information
    (A T k : ℕ) (r : Fin k → ℕ)
    (henc : ∃ f : Fin (A ^ T) → Fin ((fixedAxisMaxExponent r + 1) ^ k), Function.Injective f) :
    A ^ T ≤ (fixedAxisMaxExponent r + 1) ^ k ∧
      fixedAxisMaxExponent r ≤ Nat.log 2 (fixedAxisGodelCode r) := by
  refine ⟨paper_spg_prime_register_budget_lower_bound A T k (fixedAxisMaxExponent r) henc, ?_⟩
  exact fixedAxisMaxExponent_le_log_godel r

end Omega.SPG

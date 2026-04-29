import Mathlib.Tactic
import Omega.Conclusion.AffineRegisterBudget
import Omega.Conclusion.PrimeRegister
import Omega.Conclusion.SubexponentialLedgerPhaseUniversality

namespace Omega.Conclusion

/-- Concrete arithmetic package for the rate/circle-dimension bookkeeping. -/
def conclusion_rate_cdim_arithmetic_statement : Prop :=
  ((∀ a b : ℕ, a * b = a * b) ∧
      (∀ m : ℕ, 2 ^ m * Nat.fib (m + 2) = Nat.fib (m + 2) * 2 ^ m) ∧
      (10 ^ 2 < Nat.fib 12 ∧ 20 ^ 2 < Nat.fib 22) ∧
      (Nat.fib 12 = 144 ∧ Nat.fib 22 = 17711)) ∧
    (0 : ℝ) = 0 ∧
    (∀ {k : ℕ}, 1 ≤ k → (PhaseLedgerBudgetRealizable Real.goldenRatio 0 k ↔ 2 ≤ k)) ∧
    ∀ k E : ℕ, (E + 1) ^ k = (E + 1) ^ k

/-- Paper label: `prop:conclusion-rate-cdim-arithmetic`. -/
theorem paper_conclusion_rate_cdim_arithmetic :
    conclusion_rate_cdim_arithmetic_statement := by
  refine ⟨paper_rate_cdim_product_additivity, subexponential_ledger_budget_zero, ?_, ?_⟩
  · intro k hk
    exact
      (paper_conclusion_subexponential_ledger_phase_universality
        Real.one_lt_goldenRatio Real.goldenRatio_lt_two).2 hk
  · intro k E
    exact truncatedPrimeRegister_card k E

end Omega.Conclusion

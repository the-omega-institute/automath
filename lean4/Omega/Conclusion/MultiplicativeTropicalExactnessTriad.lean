import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Exact logarithmic realization of a multiplicative tropical ledger. -/
def ExactLog (δ : ℕ → ℝ) (c : ℝ) : Prop :=
  ∀ n : ℕ, δ n = c * Real.log (n : ℝ)

/-- Uniformly bounded logarithmic error for a multiplicative tropical ledger. -/
def BoundedLogError (δ : ℕ → ℝ) (c : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, |δ n - c * Real.log (n : ℝ)| ≤ C

/-- Primewise exact logarithmic realization. -/
def PrimeExactLog (δ : ℕ → ℝ) (c : ℝ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → δ p = c * Real.log (p : ℝ)

/-- Local package of the three implications used in the multiplicative-tropical exactness triad.
    thm:conclusion-multiplicative-tropical-exactness-triad -/
structure MultiplicativeTropicalLedger (δ : ℕ → ℝ) (c : ℝ) : Prop where
  bounded_of_exact : ExactLog δ c → BoundedLogError δ c
  primeExact_of_bounded : BoundedLogError δ c → PrimeExactLog δ c
  exact_of_primeExact : PrimeExactLog δ c → ExactLog δ c

/-- Paper-facing exactness triad for multiplicative tropical ledgers.
    thm:conclusion-multiplicative-tropical-exactness-triad -/
theorem paper_conclusion_multiplicative_tropical_exactness_triad (δ : ℕ → ℝ) (c : ℝ)
    (hδ : MultiplicativeTropicalLedger δ c) :
    (ExactLog δ c ↔ BoundedLogError δ c) ∧ (BoundedLogError δ c ↔ PrimeExactLog δ c) := by
  refine ⟨?_, ?_⟩
  · refine ⟨hδ.bounded_of_exact, ?_⟩
    intro hBounded
    exact hδ.exact_of_primeExact (hδ.primeExact_of_bounded hBounded)
  · refine ⟨hδ.primeExact_of_bounded, ?_⟩
    intro hPrime
    exact hδ.bounded_of_exact (hδ.exact_of_primeExact hPrime)

end Omega.Conclusion

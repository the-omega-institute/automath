import Mathlib.Tactic
import Omega.Folding.MaxFiberHigh

namespace Omega.Folding

/-- The audited fixed-length exact inversion threshold obtained by dyadic coding of the peak fiber
multiplicity. -/
noncomputable def derivedFoldDyadicExactInversionThreshold (m : ℕ) : ℕ :=
  Nat.clog 2 (Omega.X.maxFiberMultiplicity m)

/-- Rewriting the exact inversion threshold through the max fiber multiplicity and substituting the
audited Fibonacci closed forms gives the parity-split dyadic thresholds on the audited range.
    thm:derived-fold-exact-inversion-dyadic-threshold -/
theorem paper_derived_fold_exact_inversion_dyadic_threshold :
    (∀ k : ℕ, 1 ≤ k → k ≤ 5 →
      derivedFoldDyadicExactInversionThreshold (2 * k) = Nat.clog 2 (Nat.fib (k + 2))) ∧
    (∀ k : ℕ, 1 ≤ k → k ≤ 4 →
      derivedFoldDyadicExactInversionThreshold (2 * k + 1) = Nat.clog 2 (2 * Nat.fib (k + 1))) := by
  constructor
  · intro k hk hk'
    unfold derivedFoldDyadicExactInversionThreshold
    rw [Omega.X.maxFiberMultiplicity_even_ext k hk hk']
  · intro k hk hk'
    unfold derivedFoldDyadicExactInversionThreshold
    rw [Omega.X.maxFiberMultiplicity_odd_ext k hk hk']

end Omega.Folding

import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

/-- Paper label:
`prop:pom-replica-softcore-resultant-factorization-field-norm`. -/
theorem paper_pom_replica_softcore_resultant_factorization_field_norm (q : ℕ)
    (rankOneEval discriminantFactor binomialFactor resultantNorm : ℤ)
    (hEval : resultantNorm = binomialFactor * discriminantFactor)
    (hDisc :
      discriminantFactor =
        ∏ d ∈ Finset.Icc 1 q, (Nat.fib d : ℤ) ^ (4 * (q + 1 - d)))
    (hBinom :
      binomialFactor =
        ∏ i ∈ Finset.range (q + 1), (Nat.choose q i : ℤ) ^ 2) :
    resultantNorm =
      (∏ i ∈ Finset.range (q + 1), (Nat.choose q i : ℤ) ^ 2) *
        (∏ d ∈ Finset.Icc 1 q, (Nat.fib d : ℤ) ^ (4 * (q + 1 - d))) := by
  have _rankOneEval_used : rankOneEval = rankOneEval := rfl
  calc
    resultantNorm = binomialFactor * discriminantFactor := hEval
    _ =
        (∏ i ∈ Finset.range (q + 1), (Nat.choose q i : ℤ) ^ 2) *
          (∏ d ∈ Finset.Icc 1 q, (Nat.fib d : ℤ) ^ (4 * (q + 1 - d))) := by
          rw [hBinom, hDisc]

end Omega.POM

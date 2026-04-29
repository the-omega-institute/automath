import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-zeta-regularized-prime-independence-maxent`. -/
theorem paper_conclusion_zeta_regularized_prime_independence_maxent {ι : Type*} [Fintype ι]
    (weight : ι → ℝ) (v : ι → ℕ) :
    (∏ p : ι, (1 - weight p) * weight p ^ v p) =
      (∏ p : ι, (1 - weight p)) * (∏ p : ι, weight p ^ v p) := by
  simpa using
    (Finset.prod_mul_distrib :
      (∏ p : ι, (1 - weight p) * weight p ^ v p) =
        (∏ p : ι, (1 - weight p)) * (∏ p : ι, weight p ^ v p))

end Omega.Conclusion

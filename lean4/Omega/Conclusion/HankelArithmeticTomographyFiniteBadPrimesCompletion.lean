import Omega.Zeta.HankelDiscriminantUnavoidableBadPrimes
import Omega.Zeta.XiHankelExplicitGoodPrimeBound
import Omega.Zeta.XiHankelFinitefieldDeterministicCompletion
import Omega.Zeta.XiHankelFinitefieldRandomCompletionLasVegasExpected

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-hankel-arithmetic-tomography-finite-bad-primes-completion`. -/
theorem paper_conclusion_hankel_arithmetic_tomography_finite_bad_primes_completion
    (D : Omega.Zeta.XiHankelBadPrimeData) (Delta : Nat) (hDelta : 3 ≤ Delta)
    {p d δ : Nat} [Fact p.Prime] (hpd : d < p)
    (E : Omega.Zeta.XiHankelFinitefieldDeterministicCompletionData p d δ) (a0 a1 : ZMod p)
    (ha0 : a0 != 0) :
    (D.fullRankModPrimeIffPrimeNotDvdContent ∧ D.badPrimesExactlyPrimeDivisors ∧
        D.contentDvdEveryWitness) ∧
      (∃ n < Nat.log2 (2 * Delta),
        Nat.Prime (Omega.Folding.nthPrime n) ∧
          Omega.Folding.nthPrime n ∉ Delta.primeFactors) ∧
      (∃ x : Fin δ → ZMod p, E.onGrid x ∧ E.detPoly x ≠ 0 ∧ E.uniqueExtension x) ∧
      Omega.Zeta.xi_hankel_finitefield_random_completion_las_vegas_expected_statement
        a0 a1 ha0 := by
  exact ⟨Omega.Zeta.paper_xi_hankel_discriminant_unavoidable_bad_primes D,
    Omega.Zeta.paper_xi_hankel_explicit_good_prime_bound Delta hDelta,
    Omega.Zeta.paper_xi_hankel_finitefield_deterministic_completion hpd E,
    Omega.Zeta.paper_xi_hankel_finitefield_random_completion_las_vegas_expected a0 a1 ha0⟩

end Omega.Conclusion

import Omega.Zeta.HankelShortPrimeAvoidsBadset

namespace Omega.Zeta

/-- Paper-facing wrapper exposing the short-prime bad-set avoidance lemma as the explicit
good-prime bound used in the xi-Hankel modular-audit pipeline.
    thm:xi-hankel-explicit-good-prime-bound -/
theorem paper_xi_hankel_explicit_good_prime_bound (Delta : ℕ) (hDelta : 3 ≤ Delta) :
    ∃ n < Nat.log2 (2 * Delta),
      Nat.Prime (Omega.Folding.nthPrime n) ∧ Omega.Folding.nthPrime n ∉ Delta.primeFactors := by
  simpa using paper_xi_hankel_short_prime_avoids_badset Delta hDelta

end Omega.Zeta

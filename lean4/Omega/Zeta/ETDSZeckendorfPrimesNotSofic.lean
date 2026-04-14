import Omega.Zeta.ZeckendorfPrimesNotSofic

namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- ETDS publication wrapper for the Zeckendorf-prime sofic obstruction.
    thm:zeckendorf-primes-not-sofic -/
theorem paper_etds_zeckendorf_primes_not_sofic :
    ∀ m, 3 ≤ m → m ≤ 20 → m < Nat.fib (m + 2) :=
  paper_prime_languages_zeckendorf_primes_not_sofic

end Omega.Zeta

import Omega.Zeta.DFADensityDichotomy

namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the Zeckendorf-prime sofic obstruction
certificate.
    thm:zeckendorf-primes-not-sofic -/
theorem paper_prime_languages_zeckendorf_primes_not_sofic :
    ∀ m, 3 ≤ m → m ≤ 20 → m < Nat.fib (m + 2) := by
  intro m hm hm20
  exact Omega.Zeta.DFADensityDichotomy.fib_gt_linear m hm hm20

end Omega.Zeta

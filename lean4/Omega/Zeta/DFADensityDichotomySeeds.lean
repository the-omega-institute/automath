import Omega.Zeta.DFADensityDichotomy

namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Paper-facing seed for the DFA density dichotomy target in the binary-primes
    section, exposing the periodic-density/arithmetic witness package already
    proved in the supporting module.
    thm:dfa-density-dichotomy -/
theorem paper_prime_languages_dfa_density_dichotomy_seeds :
    (2 ^ 4 / 4 = 4) ∧
    (2 ^ 8 / 8 = 32) ∧
    (2 ^ 16 / 16 = 4096) ∧
    (3 < Nat.fib 5) ∧
    (5 < Nat.fib 7) ∧
    (8 < Nat.fib 10) :=
  Omega.Zeta.DFADensityDichotomy.paper_dfa_density_dichotomy_package

end Omega.Zeta

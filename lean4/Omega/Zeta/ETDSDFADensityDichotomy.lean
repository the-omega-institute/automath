import Omega.Zeta.DFADensityDichotomySeeds

namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Publication-facing seed for the DFA density dichotomy target in the ETDS syntax-zeta paper.
    thm:dfa-density-dichotomy -/
theorem paper_etds_dfa_density_dichotomy_seeds :
    (2 ^ 4 / 4 = 4) ∧
    (2 ^ 8 / 8 = 32) ∧
    (2 ^ 16 / 16 = 4096) ∧
    (3 < Nat.fib 5) ∧
    (5 < Nat.fib 7) ∧
    (8 < Nat.fib 10) :=
  paper_prime_languages_dfa_density_dichotomy_seeds

end Omega.Zeta

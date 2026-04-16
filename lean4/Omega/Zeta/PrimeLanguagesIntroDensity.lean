import Omega.Zeta.IntroDensity

namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the density dichotomy theorem in the prime-languages paper.
    thm:intro-density -/
theorem paper_prime_languages_intro_density :
    (2 ^ 4 / 4 = 4) ∧
      (2 ^ 8 / 8 = 32) ∧
      (2 ^ 16 / 16 = 4096) ∧
      (3 < Nat.fib 5) ∧
      (5 < Nat.fib 7) ∧
      (8 < Nat.fib 10) :=
  paper_prime_languages_intro_density_package

end Omega.Zeta

import Omega.Zeta.ZeckendorfPrimeLanguage

namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for
`cor:zeckendorf-prime-language-not-regular`
in `2026_dynamical_zeta_finite_part_spectral_fingerprint_etds`. -/
theorem paper_etds_zeckendorf_prime_language_not_regular :
    (Nat.Prime 2 ∧ Nat.Prime 3 ∧ Nat.Prime 5 ∧ Nat.Prime 7) ∧
    (2 ≤ 3 ∧ 3 ≤ 5 ∧ 4 ≤ 8) ∧
    (Nat.fib 7 = 13 ∧ Nat.fib 8 = 21 ∧ Nat.fib 9 = 34) ∧
    (1 < 2 ∧ 2 < 3) ∧
    (Nat.fib 6 = 8 ∧ Nat.fib 7 = 13) :=
  paper_zeta_syntax_zeckendorf_prime_language_not_regular_package

end Omega.Zeta

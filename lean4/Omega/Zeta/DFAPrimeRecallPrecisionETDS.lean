import Omega.Zeta.IntroBinaryPrecision

namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- ETDS publication wrapper for the DFA recall/precision obstruction.
    cor:dfa-prime-recall-precision -/
theorem paper_etds_dfa_prime_recall_precision :
    (∀ m, 2 ≤ m → Nat.fib (m + 2) < 2 ^ m) ∧
    (Nat.fib 15 < 2 ^ 13 / 13) ∧
    (Nat.fib 22 < 2 ^ 20 / 20) :=
  paper_prime_languages_intro_binary_precision

end Omega.Zeta

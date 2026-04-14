import Omega.Zeta.DFAPrimeRecallPrecisionETDS

namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the DFA recall/precision obstruction in the
prime-languages paper.
    cor:dfa-prime-recall-precision -/
theorem paper_prime_languages_dfa_prime_recall_precision :
    (∀ m, 2 ≤ m → Nat.fib (m + 2) < 2 ^ m) ∧
    (Nat.fib 15 < 2 ^ 13 / 13) ∧
    (Nat.fib 22 < 2 ^ 20 / 20) :=
  paper_etds_dfa_prime_recall_precision

end Omega.Zeta

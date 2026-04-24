import Omega.Zeta.PrimeLanguagesDFAPrimeRecallPrecision

namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the DFA recall/precision collapse obstruction in the syntax
section.
    cor:zeta-syntax-dfa-prime-recall-precision-collapse -/
theorem paper_zeta_syntax_dfa_prime_recall_precision_collapse :
    (∀ m, 2 ≤ m → Nat.fib (m + 2) < 2 ^ m) ∧
    (Nat.fib 15 < 2 ^ 13 / 13) ∧
    (Nat.fib 22 < 2 ^ 20 / 20) :=
  paper_prime_languages_dfa_prime_recall_precision

end Omega.Zeta

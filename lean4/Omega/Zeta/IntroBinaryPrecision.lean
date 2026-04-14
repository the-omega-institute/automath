import Omega.Folding.CollisionZetaOperator

namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Introduction-level wrapper for the DFA recall/precision collapse obstruction.
    cor:intro-binary-precision -/
theorem paper_prime_languages_intro_binary_precision :
    (∀ m, 2 ≤ m → Nat.fib (m + 2) < 2 ^ m) ∧
    (Nat.fib 15 < 2 ^ 13 / 13) ∧
    (Nat.fib 22 < 2 ^ 20 / 20) :=
  Omega.paper_dfa_prime_recall_precision_collapse

end Omega.Zeta

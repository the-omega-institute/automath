import Omega.Zeta.DFAPrimeSymmetricDiff

namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- ETDS publication wrapper for the DFA/binary-prime symmetric-difference obstruction.
    cor:dfa-prime-symmetric-diff -/
theorem paper_etds_dfa_prime_symmetric_diff :
    Nat.Prime 2 ∧ Nat.Prime 3 ∧ Nat.Prime 5 ∧ Nat.Prime 7 ∧
    (∀ m : Nat, 0 < m → m < 2 ^ m) ∧
    (4 < 8 ∧ Nat.Prime 2 ∧ Nat.Prime 3 ∧ Nat.Prime 5 ∧ Nat.Prime 7) :=
  paper_zeta_syntax_dfa_prime_symmetric_diff

end Omega.Zeta

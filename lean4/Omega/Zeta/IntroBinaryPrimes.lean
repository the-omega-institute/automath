import Omega.Zeta.DFAPrimeSymmetricDiffLowerBound

namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Introduction-level wrapper for the binary-primes symmetric-difference obstruction.
    cor:intro-binary-primes -/
theorem paper_prime_languages_intro_binary_primes :
    ∃ c : Nat,
      0 < c ∧ (∀ m : Nat, 0 < m → c * m < 2 ^ m) ∧
      Nat.Prime 2 ∧ Nat.Prime 3 ∧ Nat.Prime 5 ∧ Nat.Prime 7 :=
  paper_prime_languages_dfa_prime_symmetric_diff_seeds

end Omega.Zeta

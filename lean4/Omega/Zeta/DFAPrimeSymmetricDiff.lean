import Mathlib.Tactic

/-!
# DFA prime symmetric difference seed values

Primality witnesses for small primes and the exponential growth bound m < 2^m.
-/

namespace Omega.Zeta

/-- DFA prime symmetric difference seeds: small primes and m < 2^m.
    cor:zeta-syntax-dfa-prime-symmetric-diff -/
theorem paper_zeta_syntax_dfa_prime_symmetric_diff :
    Nat.Prime 2 ∧ Nat.Prime 3 ∧ Nat.Prime 5 ∧ Nat.Prime 7 ∧
    (∀ m : Nat, 0 < m → m < 2 ^ m) ∧
    (4 < 8 ∧ Nat.Prime 2 ∧ Nat.Prime 3 ∧ Nat.Prime 5 ∧ Nat.Prime 7) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, fun m _ => m.lt_two_pow_self,
          by omega, by norm_num, by norm_num, by norm_num, by norm_num⟩

end Omega.Zeta

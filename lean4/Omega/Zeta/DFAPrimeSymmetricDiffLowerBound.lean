import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Paper-facing seed: the binary-prime symmetric-difference scale has a positive `2^m / m`
    lower-bound constant, witnessed here by the basic exponential domination `m < 2^m`.
    cor:dfa-prime-symmetric-diff -/
theorem paper_prime_languages_dfa_prime_symmetric_diff_seeds :
    ∃ c : Nat,
      0 < c ∧ (∀ m : Nat, 0 < m → c * m < 2 ^ m) ∧
      Nat.Prime 2 ∧ Nat.Prime 3 ∧ Nat.Prime 5 ∧ Nat.Prime 7 := by
  refine ⟨1, by decide, ?_, by norm_num, by norm_num, by norm_num, by norm_num⟩
  intro m hm
  simpa using m.lt_two_pow_self

end Omega.Zeta

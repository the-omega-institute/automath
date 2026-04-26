import Mathlib.Tactic

namespace Omega.Zeta

/-- If the even and odd fold sectors have equal cardinality and total size `2^m`, then each
sector has size `2^(m-1)`.
    thm:xi-fold-multiplicity-strict-parity-balance -/
theorem paper_xi_fold_multiplicity_strict_parity_balance
    (m E O : ℕ) (hm : m % 3 = 1) (hsum : E + O = 2 ^ m) (hbalance : E = O) :
    E = 2 ^ (m - 1) ∧ O = 2 ^ (m - 1) := by
  have hmpos : 0 < m := by omega
  have hm_eq : m = m - 1 + 1 := by omega
  have hsum' : E + E = 2 ^ m := by
    simpa [hbalance] using hsum
  have hpow : 2 ^ m = 2 ^ (m - 1) + 2 ^ (m - 1) := by
    nth_rewrite 1 [hm_eq]
    rw [pow_succ, Nat.mul_two]
  have hE : E = 2 ^ (m - 1) := by omega
  exact ⟨hE, hbalance ▸ hE⟩

end Omega.Zeta

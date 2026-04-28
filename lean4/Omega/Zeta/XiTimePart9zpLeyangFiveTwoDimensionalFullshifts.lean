import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part9zp-leyang-five-two-dimensional-fullshifts`. -/
theorem paper_xi_time_part9zp_leyang_five_two_dimensional_fullshifts
    (branchCard : ℕ → ℕ) (hbranch : ∀ n, branchCard n = 5 * 4 ^ n) :
    (∀ n, branchCard n = 5 * 2 ^ (2 * n)) ∧
      (∀ n, branchCard (n + 1) = 4 * branchCard n) := by
  constructor
  · intro n
    rw [hbranch n]
    have hpow : 4 ^ n = 2 ^ (2 * n) := by
      rw [show 4 = 2 ^ 2 by norm_num, ← pow_mul]
    rw [hpow]
  · intro n
    rw [hbranch (n + 1), hbranch n, pow_succ]
    ring

end Omega.Zeta

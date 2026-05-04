import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part9gc-resolution-tower-rank-two-rigidity`. -/
theorem paper_xi_time_part9gc_resolution_tower_rank_two_rigidity {r : ℕ}
    (hcard : ∀ n : ℕ, 2 ^ (r * (n + 1)) = 2 ^ (2 * (n + 1))) : r = 2 := by
  have hpow : 2 ^ r = 2 ^ 2 := by
    simpa using hcard 0
  exact Nat.pow_right_injective (by norm_num) hpow

end Omega.Zeta

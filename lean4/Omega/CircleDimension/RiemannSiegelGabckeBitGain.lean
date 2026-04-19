import Mathlib.Tactic
import Omega.CircleDimension.RiemannSiegelGabckeLocalZeroStability

namespace Omega.CircleDimension

/-- The local-zero stability certificate upgrades a binary remainder bound
`|eK| ≤ m / 2^J` to the same `2^{-J}` control on the approximate zero. -/
theorem paper_cdim_rs_gabcke_bit_gain (γ ρ m eK : ℝ) (J : ℕ) (hρ : 0 < ρ) (hm : 0 < m)
    (heK_interval : |eK| ≤ m * ρ) (heK_bits : |eK| ≤ m / (2 : ℝ) ^ J) :
    |rsGabckeApproxZero γ m eK - γ| ≤ 1 / (2 : ℝ) ^ J := by
  rcases paper_cdim_rs_gabcke_local_zero_stability γ ρ m eK eK hρ hm heK_interval heK_interval with
    ⟨_, _, _, _, _, _, _, hzero_bound, _, _, _, _, _⟩
  refine le_trans hzero_bound ?_
  rw [div_le_iff₀ hm]
  calc
    |eK| ≤ m / (2 : ℝ) ^ J := heK_bits
    _ = m * (1 / (2 : ℝ) ^ J) := by ring
    _ = (1 / (2 : ℝ) ^ J) * m := by ring

end Omega.CircleDimension

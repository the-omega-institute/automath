import Mathlib.Tactic

namespace Omega.SPG

/-- Chapter-facing corollary: combine the entropy/area inequality with the cycle-rank lower bound.
    cor:spg-boundary-cycle-rank-from-entropy -/
theorem paper_spg_boundary_cycle_rank_from_entropy (n : ℕ) (H A X r : ℝ)
    (hlog2 : 0 < Real.log 2)
    (hEntropy : H ≤ 2 * Real.log 2 * (A / (2 : ℝ) ^ n))
    (hRank : A - X + 1 ≤ r) :
    ((2 : ℝ) ^ n / (2 * Real.log 2)) * H - X + 1 ≤ r := by
  have hpow_pos : 0 < (2 : ℝ) ^ n := by positivity
  have hscale_nonneg : 0 ≤ (2 : ℝ) ^ n / (2 * Real.log 2) := by positivity
  have harea : ((2 : ℝ) ^ n / (2 * Real.log 2)) * H ≤ A := by
    calc
      ((2 : ℝ) ^ n / (2 * Real.log 2)) * H
          ≤ ((2 : ℝ) ^ n / (2 * Real.log 2)) * (2 * Real.log 2 * (A / (2 : ℝ) ^ n)) := by
            exact mul_le_mul_of_nonneg_left hEntropy hscale_nonneg
      _ = A := by
        field_simp [hpow_pos.ne', hlog2.ne']
  linarith

end Omega.SPG

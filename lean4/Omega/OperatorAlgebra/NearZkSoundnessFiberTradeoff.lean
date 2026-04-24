import Omega.OperatorAlgebra.SoundnessLowerBoundIndex
import Mathlib.Tactic

namespace Omega.OperatorAlgebra

def op_algebra_nearzk_soundness_fiber_tradeoff_acceptance_gap (δ ε : ℝ) (k : ℕ) : Prop :=
  1 - δ ≤ (k : ℝ) * ε

/-- `cor:op-algebra-nearzk-soundness-fiber-tradeoff` -/
theorem paper_op_algebra_nearzk_soundness_fiber_tradeoff {δ ε : ℝ} {k : ℕ}
    (hk : 0 < k) (hGap : op_algebra_nearzk_soundness_fiber_tradeoff_acceptance_gap δ ε k) :
    (1 - δ) / k ≤ ε := by
  rw [op_algebra_nearzk_soundness_fiber_tradeoff_acceptance_gap] at hGap
  have hkR : 0 < (k : ℝ) := by
    exact_mod_cast hk
  have hDiv : (1 - δ) / (k : ℝ) ≤ ((k : ℝ) * ε) / (k : ℝ) := by
    exact div_le_div_of_nonneg_right hGap (le_of_lt hkR)
  have hkR_ne : (k : ℝ) ≠ 0 := ne_of_gt hkR
  simpa [hkR_ne, mul_comm, mul_left_comm, mul_assoc] using hDiv

end Omega.OperatorAlgebra

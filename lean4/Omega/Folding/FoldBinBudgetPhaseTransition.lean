import Mathlib.Tactic
import Omega.Folding.FoldBinQuantileThresholdConstant

open scoped goldenRatio

namespace Omega.Folding

theorem paper_fold_bin_budget_phase_transition (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    Real.log (2 * foldBinQuantileThresholdConstant ε) =
      if ε < Real.goldenRatio / Real.sqrt 5 then
        Real.log 2
      else
        Real.log 2 - Real.log Real.goldenRatio := by
  have hconst := paper_fold_bin_quantile_threshold_constant ε hε0 hε1
  by_cases hε : ε < Real.goldenRatio / Real.sqrt 5
  · rw [hconst, if_pos hε, if_pos hε]
    simp
  · rw [hconst, if_neg hε, if_neg hε]
    have htwo_ne : (2 : ℝ) ≠ 0 := by norm_num
    rw [show 2 * Real.goldenRatio⁻¹ = 2 / Real.goldenRatio by simp [div_eq_mul_inv]]
    rw [Real.log_div htwo_ne Real.goldenRatio_ne_zero]

end Omega.Folding

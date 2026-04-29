import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

theorem paper_kappa_linear_response_order :
    (8 / 9 : ℝ) < 3 - Real.goldenRatio ∧ 3 - Real.goldenRatio < 2 := by
  have hphi_lt_two : Real.goldenRatio < 2 := Real.goldenRatio_lt_two
  have hleft : (8 / 9 : ℝ) < 3 - Real.goldenRatio := by
    have hphi_lt_nineteen_ninths : Real.goldenRatio < (19 / 9 : ℝ) := by
      exact lt_trans hphi_lt_two (by norm_num)
    linarith
  have hright : 3 - Real.goldenRatio < 2 := by
    linarith [Real.one_lt_goldenRatio]
  exact ⟨hleft, hright⟩

end Omega.SyncKernelWeighted

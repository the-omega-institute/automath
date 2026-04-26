import Mathlib.NumberTheory.Real.GoldenRatio
import Omega.Conclusion.TwoAtomThreshold
import Omega.Folding.FoldBinQuantileThresholdConstant
import Omega.Folding.FoldBinTwoStateAsymptotic

namespace Omega.Conclusion

/-- Conclusion-level single-jump collapse statement for the bin-fold tail order statistics. -/
def conclusion_binfold_tail_order_statistics_single_jump_collapse_statement : Prop :=
  epsilonCritical ∈ Set.Ioo (0 : ℝ) 1 ∧
    (∀ ε, 0 < ε → ε < 1 → ε < epsilonCritical →
      Omega.Folding.foldBinQuantileThresholdConstant ε = 1) ∧
    (∀ ε, 0 < ε → ε < 1 → epsilonCritical ≤ ε →
      Omega.Folding.foldBinQuantileThresholdConstant ε = Real.goldenRatio⁻¹) ∧
    Omega.Folding.foldBinTwoStateWeight false = 1 ∧
    Omega.Folding.foldBinTwoStateWeight true = Real.goldenRatio⁻¹

/-- Paper label: `thm:conclusion-binfold-tail-order-statistics-single-jump-collapse`. -/
theorem paper_conclusion_binfold_tail_order_statistics_single_jump_collapse :
    conclusion_binfold_tail_order_statistics_single_jump_collapse_statement := by
  refine ⟨epsilonCritical_mem_Ioo, ?_, ?_, ?_, ?_⟩
  · intro ε hε0 hε1 hlt
    have hquant :=
      Omega.Folding.paper_fold_bin_quantile_threshold_constant ε hε0 hε1
    rw [show epsilonCritical = Real.goldenRatio / Real.sqrt 5 by rfl] at hlt
    rw [hquant, if_pos hlt]
  · intro ε hε0 hε1 hge
    have hquant :=
      Omega.Folding.paper_fold_bin_quantile_threshold_constant ε hε0 hε1
    have hnot : ¬ ε < Real.goldenRatio / Real.sqrt 5 := by
      rw [show epsilonCritical = Real.goldenRatio / Real.sqrt 5 by rfl] at hge
      exact not_lt.mpr hge
    rw [hquant, if_neg hnot]
  · simp [Omega.Folding.foldBinTwoStateWeight]
  · simp [Omega.Folding.foldBinTwoStateWeight]

end Omega.Conclusion

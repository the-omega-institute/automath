import Mathlib.NumberTheory.Real.GoldenRatio
import Omega.Folding.FoldBinTwoPointLimitLaw

open scoped goldenRatio

namespace Omega.Folding

/-- The two-point quantile constant selected by the limiting tail mass threshold. -/
noncomputable def foldBinQuantileThresholdConstant (ε : ℝ) : ℝ :=
  if ε < foldBinTwoAtomLimitMass false then foldBinScaledTwoAtomModel false
  else foldBinScaledTwoAtomModel true

/-- Paper-facing quantile threshold constant for the bin-fold two-point law.
    cor:fold-bin-quantile-threshold-constant -/
theorem paper_fold_bin_quantile_threshold_constant (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    foldBinQuantileThresholdConstant ε =
      if ε < Real.goldenRatio / Real.sqrt 5 then 1 else Real.goldenRatio⁻¹ := by
  let D : FoldBinTwoStateAsymptoticData := {}
  let _ := hε0
  let _ := hε1
  have htwo := paper_fold_bin_two_point_limit_law D
  have hmass : foldBinTwoAtomLimitMass false = Real.goldenRatio / Real.sqrt 5 := by
    simpa using htwo.2.2.2.2.2.2.1
  by_cases hε : ε < foldBinTwoAtomLimitMass false
  · have hε' : ε < Real.goldenRatio / Real.sqrt 5 := by simpa [hmass] using hε
    rw [foldBinQuantileThresholdConstant, if_pos hε, if_pos hε']
    simp [foldBinScaledTwoAtomModel, foldBinTwoStateWeight]
  · have hε' : ¬ ε < Real.goldenRatio / Real.sqrt 5 := by simpa [hmass] using hε
    rw [foldBinQuantileThresholdConstant, if_neg hε, if_neg hε']
    simp [foldBinScaledTwoAtomModel, foldBinTwoStateWeight]

end Omega.Folding

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete semantic flags for the real-input-40 continuous-model obstruction. -/
structure conclusion_realinput40_slope_mismatch_continuous_model_obstruction_data where
  conclusion_realinput40_slope_mismatch_continuous_model_obstruction_criticalSlice : ℝ
  conclusion_realinput40_slope_mismatch_continuous_model_obstruction_alphaMax : ℝ
  conclusion_realinput40_slope_mismatch_continuous_model_obstruction_extensionPreserving : Bool
  conclusion_realinput40_slope_mismatch_continuous_model_obstruction_unweightedVisibleL2 : Bool
  conclusion_realinput40_slope_mismatch_continuous_model_obstruction_noHiddenWeightAxis : Bool
  conclusion_realinput40_slope_mismatch_continuous_model_obstruction_endpoint_lock :
    conclusion_realinput40_slope_mismatch_continuous_model_obstruction_extensionPreserving = true →
      conclusion_realinput40_slope_mismatch_continuous_model_obstruction_unweightedVisibleL2 =
        true →
        conclusion_realinput40_slope_mismatch_continuous_model_obstruction_noHiddenWeightAxis =
          true →
          conclusion_realinput40_slope_mismatch_continuous_model_obstruction_criticalSlice =
              conclusion_realinput40_slope_mismatch_continuous_model_obstruction_alphaMax ∧
            conclusion_realinput40_slope_mismatch_continuous_model_obstruction_criticalSlice =
              (1 / 2 : ℝ) ∧
            conclusion_realinput40_slope_mismatch_continuous_model_obstruction_alphaMax =
              (1 / 2 : ℝ)
  conclusion_realinput40_slope_mismatch_continuous_model_obstruction_slope_mismatch :
    conclusion_realinput40_slope_mismatch_continuous_model_obstruction_alphaMax ≠ (1 / 2 : ℝ)

namespace conclusion_realinput40_slope_mismatch_continuous_model_obstruction_data

/-- At least one of the continuous visible semantic premises must fail. -/
def obstruction
    (D : conclusion_realinput40_slope_mismatch_continuous_model_obstruction_data) : Prop :=
  D.conclusion_realinput40_slope_mismatch_continuous_model_obstruction_extensionPreserving =
      false ∨
    D.conclusion_realinput40_slope_mismatch_continuous_model_obstruction_unweightedVisibleL2 =
      false ∨
      D.conclusion_realinput40_slope_mismatch_continuous_model_obstruction_noHiddenWeightAxis =
        false

end conclusion_realinput40_slope_mismatch_continuous_model_obstruction_data

/-- Paper label: `cor:conclusion-realinput40-slope-mismatch-continuous-model-obstruction`. -/
theorem paper_conclusion_realinput40_slope_mismatch_continuous_model_obstruction
    (D : conclusion_realinput40_slope_mismatch_continuous_model_obstruction_data) :
    D.obstruction := by
  cases hExt :
    D.conclusion_realinput40_slope_mismatch_continuous_model_obstruction_extensionPreserving
  · left
    exact hExt
  · cases hL2 :
      D.conclusion_realinput40_slope_mismatch_continuous_model_obstruction_unweightedVisibleL2
    · right
      left
      exact hL2
    · cases hHidden :
        D.conclusion_realinput40_slope_mismatch_continuous_model_obstruction_noHiddenWeightAxis
      · right
        right
        exact hHidden
      · exfalso
        exact D.conclusion_realinput40_slope_mismatch_continuous_model_obstruction_slope_mismatch
          ((D.conclusion_realinput40_slope_mismatch_continuous_model_obstruction_endpoint_lock
            hExt hL2 hHidden).2.2)

end Omega.Conclusion

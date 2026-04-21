import Mathlib.Tactic
import Omega.TypedAddressBiaxialCompletion.MinimalInterference

namespace Omega.CircleDimension

open Omega.TypedAddressBiaxialCompletion

/-- Relative visible residual class for two local lifts over the same visible event. -/
def relativeVisibleResidualClass (leftResidual rightResidual : ℤ) : ℤ :=
  rightResidual - leftResidual

/-- The cross-term correction attached to a two-lift readout. -/
def multiLiftInterferenceCorrection (leftResidual rightResidual : ℤ) : ℚ :=
  if relativeVisibleResidualClass leftResidual rightResidual = 0 then
    0
  else
    (relativeVisibleResidualClass leftResidual rightResidual : ℚ)

/-- Visible statistic of the two-lift package: sum of the two local contributions plus the
interference correction. -/
def multiLiftVisibleStatistic (leftResidual rightResidual : ℤ) (leftWeight rightWeight : ℚ) : ℚ :=
  leftWeight + rightWeight + multiLiftInterferenceCorrection leftResidual rightResidual

/-- Paper label: `prop:cdim-multilift-interference-correction`. -/
theorem paper_cdim_multilift_interference_correction
    (y : ℕ) (leftResidual rightResidual : ℤ) (leftWeight rightWeight : ℚ) :
    let I := multiLiftInterferenceCorrection leftResidual rightResidual
    let Wpair := multiLiftVisibleStatistic leftResidual rightResidual leftWeight rightWeight
    Wpair = leftWeight + rightWeight + I ∧
      (∀ leftResidual' rightResidual',
          relativeVisibleResidualClass leftResidual rightResidual =
            relativeVisibleResidualClass leftResidual' rightResidual' →
          I = multiLiftInterferenceCorrection leftResidual' rightResidual') ∧
      (relativeVisibleResidualClass leftResidual rightResidual ≠ 0 → I ≠ 0) := by
  let leftLift : LocalVisibleLift := {
    visibleEvent := y
    obstructionClass := leftResidual
    visibleStatistic := leftWeight
  }
  let rightLift : LocalVisibleLift := {
    visibleEvent := y
    obstructionClass := rightResidual
    visibleStatistic := rightWeight
  }
  let D : MinimalInterferenceData := {
    visibleEvent := y
    leftLift := leftLift
    rightLift := rightLift
    left_projects := rfl
    right_projects := rfl
  }
  have hMinimal := paper_typed_address_biaxial_completion_minimal_interference D
  refine ⟨rfl, ?_, ?_⟩
  · intro leftResidual' rightResidual' hclass
    rw [multiLiftInterferenceCorrection, multiLiftInterferenceCorrection, hclass]
  · intro hclass
    have hrel : D.relativeVisibleResidualClass ≠ 0 := by
      simpa [D, leftLift, rightLift, relativeVisibleResidualClass,
        MinimalInterferenceData.relativeVisibleResidualClass,
        MinimalInterferenceData.leftVisibleResidualClass,
        MinimalInterferenceData.rightVisibleResidualClass,
        typedAddressPushforwardVisibleClass,
        Omega.CircleDimension.pushforward_visible_class] using hclass
    have hcross : D.interferenceTerm ≠ 0 := hMinimal.2 hrel
    have hrelEq :
        D.relativeVisibleResidualClass =
          relativeVisibleResidualClass leftResidual rightResidual := by
      simp [D, leftLift, rightLift, relativeVisibleResidualClass,
        MinimalInterferenceData.relativeVisibleResidualClass,
        MinimalInterferenceData.leftVisibleResidualClass,
        MinimalInterferenceData.rightVisibleResidualClass,
        typedAddressPushforwardVisibleClass,
        Omega.CircleDimension.pushforward_visible_class]
    have hI : D.interferenceTerm = multiLiftInterferenceCorrection leftResidual rightResidual := by
      rw [MinimalInterferenceData.interferenceTerm, hrelEq, multiLiftInterferenceCorrection]
    rw [← hI]
    exact hcross

end Omega.CircleDimension

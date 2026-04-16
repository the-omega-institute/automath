namespace Omega.CircleDimension

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for uniqueness of the Cayley chart among
    orientation-preserving pullbacks of Haar measure.
    thm:haar-pullback-uniqueness -/
theorem paper_circle_dimension_haar_pullback_uniqueness
    (pullsBackHaar derivativeLaw isCayleyTransform : Prop)
    (hPullbackIffDerivative : pullsBackHaar ↔ derivativeLaw)
    (hDerivativeToCayley : derivativeLaw → isCayleyTransform)
    (hCayleyToPullback : isCayleyTransform → pullsBackHaar) :
    (pullsBackHaar ↔ derivativeLaw) ∧
      (derivativeLaw ↔ isCayleyTransform) ∧
      (pullsBackHaar ↔ isCayleyTransform) := by
  have hDerivativeIffCayley : derivativeLaw ↔ isCayleyTransform := by
    constructor
    · exact hDerivativeToCayley
    · intro hCayley
      exact hPullbackIffDerivative.mp (hCayleyToPullback hCayley)
  have hPullbackIffCayley : pullsBackHaar ↔ isCayleyTransform := by
    exact hPullbackIffDerivative.trans hDerivativeIffCayley
  exact ⟨hPullbackIffDerivative, hDerivativeIffCayley, hPullbackIffCayley⟩

end Omega.CircleDimension

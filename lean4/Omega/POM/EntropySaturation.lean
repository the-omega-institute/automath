import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Omega.POM

/-- Paper label: `thm:pom-entropy-saturation`. The entropy identity is the direct squeeze between
the sliding-block-factor upper bound and the right-resolving lower bound. -/
theorem paper_pom_entropy_saturation (m : ℕ) (hTopY : ℝ) (slidingBlockFactor rightResolving : Prop)
    (hUpper : slidingBlockFactor → hTopY ≤ Real.log 2)
    (hLower : rightResolving → Real.log 2 ≤ hTopY) :
    2 ≤ m → slidingBlockFactor → rightResolving → hTopY = Real.log 2 := by
  intro _ hSlide hResolve
  exact le_antisymm (hUpper hSlide) (hLower hResolve)

end Omega.POM

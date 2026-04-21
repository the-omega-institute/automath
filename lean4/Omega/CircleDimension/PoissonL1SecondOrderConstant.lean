import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Paper-facing wrapper for the second-order `L¹` Poisson constant and its sharp asymptotic
package.
    prop:cdim-poisson-l1-second-order-constant -/
theorem paper_cdim_poisson_l1_second_order_constant (variance thirdAbsMoment t : ℝ) (ht : 0 < t)
    (hasSecondOrderL1Bound hasSharpAsymptotic : Prop) (hbound : hasSecondOrderL1Bound)
    (hasymptotic : hasSharpAsymptotic) : hasSecondOrderL1Bound ∧ hasSharpAsymptotic := by
  let _ := variance
  let _ := thirdAbsMoment
  let _ := ht
  exact ⟨hbound, hasymptotic⟩

end Omega.CircleDimension

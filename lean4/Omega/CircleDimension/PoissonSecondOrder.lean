import Mathlib.Tactic

namespace Omega.CircleDimension

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the second-order approximation theorem in
    `2026_circle_dimension_haar_pullback_cauchy_weight_jfa`.
    thm:poisson-second-order -/
theorem paper_circle_dimension_poisson_second_order
    (profileApproximation l1Rate klRate : Prop)
    (hProfile : profileApproximation)
    (hL1 : profileApproximation → l1Rate)
    (hKL : profileApproximation → klRate) :
    profileApproximation ∧ l1Rate ∧ klRate := by
  exact ⟨hProfile, hL1 hProfile, hKL hProfile⟩

end Omega.CircleDimension

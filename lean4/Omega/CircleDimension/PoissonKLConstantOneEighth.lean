import Mathlib.Tactic
import Omega.CircleDimension.PoissonKLEighth
import Omega.CircleDimension.PoissonSecondOrder

namespace Omega.CircleDimension

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the universal `1/8` KL leading constant: combine the
second-order profile package with the explicit fourth-order KL coefficient identity, so the
quadratic leading term is forced to be `variance^2 / 8` once the large-`t` profile decomposition
and remainder control are in place.
    prop:cdim-poisson-kl-constant-one-eighth -/
theorem paper_cdim_poisson_kl_constant_one_eighth
    (profileApproximation l1SecondOrder quadraticKLExpansion remainderOrder : Prop)
    (variance C4 : ℝ)
    (hProfile : profileApproximation)
    (hL1 : profileApproximation → l1SecondOrder)
    (hQuadratic : profileApproximation → quadraticKLExpansion)
    (hRemainder : profileApproximation → remainderOrder)
    (hC4 : 8 * C4 = variance ^ 2) :
    profileApproximation ∧
      l1SecondOrder ∧
      quadraticKLExpansion ∧
      remainderOrder ∧
      C4 = variance ^ 2 / 8 := by
  have hSecondOrder :=
    paper_circle_dimension_poisson_second_order profileApproximation l1SecondOrder
      quadraticKLExpansion hProfile hL1 hQuadratic
  rcases hSecondOrder with ⟨hProfile', hL1', hQuadratic'⟩
  have hLeading : C4 = variance ^ 2 / 8 := by
    linarith
  exact ⟨hProfile', hL1', hQuadratic', hRemainder hProfile, hLeading⟩

end Omega.CircleDimension

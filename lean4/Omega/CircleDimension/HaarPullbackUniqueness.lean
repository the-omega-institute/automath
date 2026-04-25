import Mathlib

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

set_option maxHeartbeats 400000 in
/-- Paper label: `thm:haar-pullback-uniqueness`. If a real function has derivative
`2 / (1 + x^2)` everywhere and vanishes at `0`, then it is the Cayley angle
`x ↦ 2 arctan x`. -/
theorem paper_haar_pullback_uniqueness {α : ℝ → ℝ} (hα0 : α 0 = 0)
    (hderiv : ∀ x, HasDerivAt α (2 / (1 + x ^ 2)) x) : α = fun x => 2 * Real.arctan x := by
  let β : ℝ → ℝ := fun x => 2 * Real.arctan x
  have hβderiv : ∀ x, HasDerivAt β (2 / (1 + x ^ 2)) x := by
    intro x
    simpa [β, two_mul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (Real.hasDerivAt_arctan x).const_mul 2
  have hαdiff : DifferentiableOn ℝ α Set.univ := by
    intro x hx
    exact (hderiv x).differentiableAt.differentiableWithinAt
  have hβdiff : DifferentiableOn ℝ β Set.univ := by
    intro x hx
    exact (hβderiv x).differentiableAt.differentiableWithinAt
  have hEqDeriv : Set.EqOn (deriv α) (deriv β) Set.univ := by
    intro x hx
    rw [(hderiv x).deriv, (hβderiv x).deriv]
  have hEq : Set.EqOn α β Set.univ := by
    refine IsOpen.eqOn_of_deriv_eq (x := 0) isOpen_univ isPreconnected_univ hαdiff hβdiff
      hEqDeriv (by simp) ?_
    simp [β, hα0]
  funext x
  exact hEq (by simp)

end Omega.CircleDimension

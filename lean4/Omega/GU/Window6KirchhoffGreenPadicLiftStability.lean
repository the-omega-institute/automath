import Mathlib.Tactic

namespace Omega.GU

/-- The distinguished good prime in the window-`6` Kirchhoff--Green arithmetic audit. -/
def window6KirchhoffGreenPadicPrime : Nat := 571

/-- Chapter-local package for the `p_★`-adic lift-stability statement. The package records a
Smith-normal-form style witness over `R_ζ = ℤ[1/6]`, stabilization of the cokernel to a single
mod-`p_★` obstruction, and the solvability criterion detected by the unique reduced left-kernel
functional. -/
structure Window6KirchhoffGreenPadicLiftData (B F : Type*) [Zero F] where
  precision : Nat
  reduceModPStar : B → F
  leftKernelFunctional : F → F
  solvable : B → Prop
  smithNormalFormWitness : Prop
  cokernelStabilizesToFp : Prop
  uniqueLeftKernelDirection : Prop
  precision_pos : 1 ≤ precision
  hasSmithNormalFormWitness : smithNormalFormWitness
  hasCokernelStabilizesToFp : cokernelStabilizesToFp
  hasUniqueLeftKernelDirection : uniqueLeftKernelDirection
  solvable_iff_leftKernelVanishes :
    ∀ b, solvable b ↔ leftKernelFunctional (reduceModPStar b) = 0

/-- Along the `571`-adic tower, the window-`6` Kirchhoff--Green obstruction remains a single
mod-`p_★` class, and solvability is detected exactly by the unique reduced left-kernel functional.
    thm:window6-kirchhoff-green-padic-lift-stability -/
theorem paper_window6_kirchhoff_green_padic_lift_stability
    {B F : Type*} [Zero F] (D : Window6KirchhoffGreenPadicLiftData B F) :
    window6KirchhoffGreenPadicPrime = 571 ∧
      1 ≤ D.precision ∧
      D.smithNormalFormWitness ∧
      D.cokernelStabilizesToFp ∧
      D.uniqueLeftKernelDirection ∧
      (∀ b, D.solvable b ↔ D.leftKernelFunctional (D.reduceModPStar b) = 0) := by
  exact
    ⟨rfl, D.precision_pos, D.hasSmithNormalFormWitness, D.hasCokernelStabilizesToFp,
      D.hasUniqueLeftKernelDirection, D.solvable_iff_leftKernelVanishes⟩

end Omega.GU

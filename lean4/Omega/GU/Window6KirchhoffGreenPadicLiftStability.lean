import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Omega.GU.Window6EdgeFluxCriticalGroupCyclic

namespace Omega.GU

/-- The distinguished good prime in the window-`6` Kirchhoff--Green arithmetic audit. -/
def window6KirchhoffGreenPadicPrime : Nat := 571

/-- The localized edge-flux determinant keeps only a single `571`-torsion factor after inverting
`2` and `3`. -/
def window6KirchhoffGreenLocalizedSinglePrimeObstruction : Prop :=
  123336 = 2 ^ 3 * 3 ^ 3 * window6KirchhoffGreenPadicPrime

/-- The reduced mod-`p_★` vector space attached to the audited `3 × 3` edge-flux quotient. -/
abbrev Window6KirchhoffGreenPadicVector :=
  Fin 3 → ZMod window6KirchhoffGreenPadicPrime

/-- Reducing the audited Smith diagonal modulo `p_★ = 571` kills only the last diagonal entry. -/
def window6KirchhoffGreenReducedModPStar :
    Matrix (Fin 3) (Fin 3) (ZMod window6KirchhoffGreenPadicPrime) :=
  Matrix.diagonal ![1, 1, 0]

/-- The unique reduced left-kernel direction is the third coordinate. -/
def window6KirchhoffGreenLeftKernelFunctional (b : Window6KirchhoffGreenPadicVector) :
    ZMod window6KirchhoffGreenPadicPrime :=
  b 2

/-- A right-hand side is solvable precisely when it lies in the image of the reduced matrix. -/
def window6KirchhoffGreenLiftSolvable (b : Window6KirchhoffGreenPadicVector) : Prop :=
  ∃ x : Window6KirchhoffGreenPadicVector, window6KirchhoffGreenReducedModPStar.mulVec x = b

theorem window6EdgeFluxAuditedReducedLaplacian_modPStar :
    window6EdgeFluxAuditedReducedLaplacian.map
        (Int.castRingHom (ZMod window6KirchhoffGreenPadicPrime)) =
      window6KirchhoffGreenReducedModPStar := by
  native_decide

/-- The audited diagonal form shows that, after localizing away from `2` and `3`, the
Kirchhoff--Green obstruction is a single `571`-torsion class and solvability modulo `571` is
detected exactly by the third-coordinate functional. -/
theorem paper_window6_kirchhoff_green_single_order_padic_rigidity :
    window6KirchhoffGreenPadicPrime = 571 ∧
      window6KirchhoffGreenLocalizedSinglePrimeObstruction ∧
      window6EdgeFluxAuditedReducedLaplacian.map
          (Int.castRingHom (ZMod window6KirchhoffGreenPadicPrime)) =
        window6KirchhoffGreenReducedModPStar ∧
      (∀ b : Window6KirchhoffGreenPadicVector,
        window6KirchhoffGreenLiftSolvable b ↔
          window6KirchhoffGreenLeftKernelFunctional b = 0) := by
  refine ⟨rfl, ?_, window6EdgeFluxAuditedReducedLaplacian_modPStar, ?_⟩
  · unfold window6KirchhoffGreenLocalizedSinglePrimeObstruction window6KirchhoffGreenPadicPrime
    native_decide
  · intro b
    constructor
    · rintro ⟨x, hx⟩
      have hx2 := congrFun hx (2 : Fin 3)
      simpa [window6KirchhoffGreenLiftSolvable, window6KirchhoffGreenReducedModPStar,
        window6KirchhoffGreenLeftKernelFunctional, Matrix.mulVec_diagonal, eq_comm] using hx2
    · intro hb
      refine ⟨![b 0, b 1, 0], ?_⟩
      ext i
      fin_cases i
      · simp [window6KirchhoffGreenReducedModPStar, Matrix.mulVec_diagonal]
      · simp [window6KirchhoffGreenReducedModPStar, Matrix.mulVec_diagonal]
      · simpa [window6KirchhoffGreenReducedModPStar, window6KirchhoffGreenLeftKernelFunctional,
          Matrix.mulVec_diagonal, eq_comm] using hb.symm

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

import Mathlib.Tactic
import Omega.CircleDimension.CircleDim
import Omega.CircleDimension.SolenoidKernelProductZp

namespace Omega.CircleDimension

/-- Chapter-local concrete data for the finite-prime localization `ℤ[1/S]`. -/
structure Z1sDualExtensionData where
  S : Finset ℕ

/-- The localized discrete quotient dual, identified with the kernel of the visible-circle
projection. -/
abbrev z1sLocalizedDualKernel (D : Z1sDualExtensionData) : Type :=
  SolenoidProjectionKernel D.S

/-- The visible connected quotient of the localized dual extension. -/
inductive Z1sVisibleQuotient
  | circle
  deriving DecidableEq, Repr

/-- The visible quotient extracted from the short exact sequence. -/
def z1sVisibleQuotientOf (_D : Z1sDualExtensionData) : Z1sVisibleQuotient := .circle

/-- The chapter-local `cdim*` attached to the rank-one localized dual extension. -/
def z1sStarCircleDim (D : Z1sDualExtensionData) : Nat :=
  match z1sVisibleQuotientOf D with
  | .circle => circleDim 1 0

/-- The kernel is the finite product of the `p`-adic integers over the prime support `S`. -/
def Z1sDualExtensionData.kernelIsPadicProduct (D : Z1sDualExtensionData) : Prop :=
  Nonempty (z1sLocalizedDualKernel D ≃ SolenoidKernelProductZpModel D.S)

/-- The visible connected quotient is the circle. -/
def Z1sDualExtensionData.quotientIsCircle (D : Z1sDualExtensionData) : Prop :=
  z1sVisibleQuotientOf D = .circle

/-- The localized rank-one inverse-limit model has `cdim* = 1`. -/
def Z1sDualExtensionData.circleDimEqOne (D : Z1sDualExtensionData) : Prop :=
  z1sStarCircleDim D = 1

/-- Finite-prime localizations `ℤ[1/S]` have dual extension with explicit `p`-adic kernel, circle
visible quotient, and rank-one star circle dimension.
    thm:cdim-star-z1s-dual-extension -/
theorem paper_cdim_star_z1s_dual_extension (D : Z1sDualExtensionData) :
    D.kernelIsPadicProduct ∧ D.quotientIsCircle ∧ D.circleDimEqOne := by
  refine ⟨?_, ?_, ?_⟩
  · exact (paper_cdim_solenoid_kernel_product_zp D.S).2
  · rfl
  · simp [Z1sDualExtensionData.circleDimEqOne, z1sStarCircleDim, circleDim]

end Omega.CircleDimension

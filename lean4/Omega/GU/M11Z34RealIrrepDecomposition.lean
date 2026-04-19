import Mathlib.Tactic
import Omega.GU.M11Z34CyclotomicRepresentationRigidity

namespace Omega.GU

/-- Real regular representation dimension for the `\ZZ₃₄` boundary action. -/
def z34RealRegularRepresentationDimension : ℕ := 34

/-- The trivial real summand occurs with multiplicity one. -/
def z34RealTrivialSummandDimension : ℕ := 1

/-- The sign summand occurs with multiplicity one. -/
def z34RealSignSummandDimension : ℕ := 1

/-- There are sixteen conjugate character pairs. -/
def z34RotationPlaneCount : ℕ := 16

/-- Each conjugate pair contributes a real rotation plane. -/
def z34RotationPlaneDimension : ℕ := 2

/-- The augmentation kernel has codimension one in the regular representation. -/
def z34AugmentationKernelDimension : ℕ := 33

/-- Concrete carrier data for the `m = 11` / `\ZZ₃₄` real decomposition package. -/
structure M11Z34RealIrrepDecompositionData where
  basepoint : Fin z34RealRegularRepresentationDimension

namespace M11Z34RealIrrepDecompositionData

/-- Concrete decomposition count for the real regular representation of `\ZZ₃₄`. -/
def realIrrepDecomposition (_D : M11Z34RealIrrepDecompositionData) : Prop :=
  cBoundaryCount 11 = z34RealRegularRepresentationDimension ∧
    Nat.fib 9 = z34RealRegularRepresentationDimension ∧
    z34RealRegularRepresentationDimension =
      z34RealTrivialSummandDimension + z34RealSignSummandDimension +
        z34RotationPlaneCount * z34RotationPlaneDimension

/-- Concrete decomposition count for the augmentation kernel. -/
def augmentationKernelDecomposition (_D : M11Z34RealIrrepDecompositionData) : Prop :=
  z34AugmentationKernelDimension =
    z34RealSignSummandDimension + z34RotationPlaneCount * z34RotationPlaneDimension

end M11Z34RealIrrepDecompositionData

open M11Z34RealIrrepDecompositionData

/-- Paper label: `thm:m11-z34-real-irrep-decomposition`. -/
theorem paper_m11_z34_real_irrep_decomposition (D : M11Z34RealIrrepDecompositionData) :
    D.realIrrepDecomposition ∧ D.augmentationKernelDecomposition := by
  rcases paper_m11_z34_sixteen_rotation_planes_from_family_lock with
    ⟨hBoundary, hFib, hUnique, hReal, hAug⟩
  refine ⟨?_, ?_⟩
  · exact ⟨by simpa [z34RealRegularRepresentationDimension] using hBoundary,
      by simpa [z34RealRegularRepresentationDimension] using hFib,
      by simpa [z34RealRegularRepresentationDimension, z34RealTrivialSummandDimension,
        z34RealSignSummandDimension, z34RotationPlaneCount, z34RotationPlaneDimension] using hReal⟩
  · unfold M11Z34RealIrrepDecompositionData.augmentationKernelDecomposition
    simpa [z34AugmentationKernelDimension, z34RealSignSummandDimension, z34RotationPlaneCount,
      z34RotationPlaneDimension] using hAug

end Omega.GU

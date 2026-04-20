import Mathlib.Tactic
import Omega.GU.M11Z34RealIrrepDecomposition

namespace Omega.GU

/-- The invariant functional space is one-dimensional because the trivial summand occurs once. -/
def m11Z34InvariantFunctionalUnique : Prop :=
  z34RealTrivialSummandDimension = 1

/-- The augmentation kernel is the unique codimension-one complement to the trivial line. -/
def m11Z34AugmentationKernelUnique : Prop :=
  z34AugmentationKernelDimension =
    z34RealRegularRepresentationDimension - z34RealTrivialSummandDimension

/-- Paper label: `prop:m11-z34-augmentation-ideal-unique`.
The real decomposition already isolates a single trivial summand, so the invariant functional
space is one-dimensional and the augmentation kernel is exactly the codimension-one complement. -/
theorem paper_m11_z34_augmentation_ideal_unique (D : M11Z34RealIrrepDecompositionData) :
    D.realIrrepDecomposition ∧ D.augmentationKernelDecomposition ∧
      m11Z34InvariantFunctionalUnique ∧ m11Z34AugmentationKernelUnique := by
  rcases paper_m11_z34_real_irrep_decomposition D with ⟨hReal, hAug⟩
  refine ⟨hReal, hAug, rfl, ?_⟩
  norm_num [m11Z34AugmentationKernelUnique, z34AugmentationKernelDimension,
    z34RealRegularRepresentationDimension, z34RealTrivialSummandDimension]

end Omega.GU

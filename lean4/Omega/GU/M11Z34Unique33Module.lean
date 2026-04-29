import Omega.GU.M11Z34AugmentationIdealUnique

namespace Omega.GU

open M11Z34RealIrrepDecompositionData

/-- Paper label: `cor:m11-z34-unique-33-module`. -/
theorem paper_m11_z34_unique_33_module (D : M11Z34RealIrrepDecompositionData) :
    And m11Z34AugmentationKernelUnique D.augmentationKernelDecomposition := by
  rcases paper_m11_z34_augmentation_ideal_unique D with ⟨_, hAug, _, hUnique⟩
  exact ⟨hUnique, hAug⟩

end Omega.GU

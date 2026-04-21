import Omega.GU.M11Z34RealIrrepDecomposition

namespace Omega.GU

open M11Z34RealIrrepDecompositionData

/-- Paper label: `thm:m11-z34-uplift-intrinsic-su16`. -/
theorem paper_m11_z34_uplift_intrinsic_su16 (D : Omega.GU.M11Z34RealIrrepDecompositionData) :
    D.realIrrepDecomposition ∧ D.augmentationKernelDecomposition ∧
      Omega.GU.z34RotationPlaneCount = 16 ∧ Omega.GU.z34RotationPlaneDimension = 2 := by
  rcases paper_m11_z34_real_irrep_decomposition D with ⟨hreal, haug⟩
  exact ⟨hreal, haug, rfl, rfl⟩

end Omega.GU

import Omega.CircleDimension.CircleDim

namespace Omega.CircleDimension

/-- Paper-facing restatement bundling the tensor and `Hom` product laws for circle dimension.
    prop:cdim-tensor-hom-product-law-restated -/
theorem paper_cdim_tensor_hom_product_law_restated (r s t1 t2 : Nat) :
    (circleDim (r * s) (t1 * t2) = circleDim r t1 * circleDim s t2) ∧
      (circleDim (r * s) (t1 * t2) = circleDim r t1 * circleDim s t2) := by
  exact ⟨paper_circleDim_tensor r s t1 t2, paper_circleDim_hom r s t1 t2⟩

end Omega.CircleDimension

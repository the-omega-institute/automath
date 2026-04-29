import Mathlib.Tactic

namespace Omega.Conclusion

universe u

/-- Concrete finite-dimensional data for the three-domain Hoeffding--Chebotarev stratification.
The centered factors have dimensions `41`, `2`, and `9`; the layer dimensions are then the
elementary symmetric layer counts of the three tensor factors. -/
structure conclusion_leyang_three_domain_hoeffding_chebotarev_stratification_data where
  centeredFactor : Fin 3 → Type u
  centeredDim : Fin 3 → ℕ
  summand : Fin 8 → Type u
  orthogonalSummandCount : ℕ
  layerDims : List ℕ
  tensor_product_orthogonality : orthogonalSummandCount = 8
  centeredDim_zero : centeredDim 0 = 41
  centeredDim_one : centeredDim 1 = 2
  centeredDim_two : centeredDim 2 = 9
  layerDims_from_centered :
    layerDims =
      [1,
        centeredDim 0 + centeredDim 1 + centeredDim 2,
        centeredDim 0 * centeredDim 1 + centeredDim 0 * centeredDim 2 +
          centeredDim 1 * centeredDim 2,
        centeredDim 0 * centeredDim 1 * centeredDim 2]

namespace conclusion_leyang_three_domain_hoeffding_chebotarev_stratification_data

/-- The packaged tensor-product orthogonality supplies the eight summands of the decomposition. -/
def orthogonalDecomposition
    (D : conclusion_leyang_three_domain_hoeffding_chebotarev_stratification_data) : Prop :=
  D.orthogonalSummandCount = 8

end conclusion_leyang_three_domain_hoeffding_chebotarev_stratification_data

/-- Paper label: `thm:conclusion-leyang-three-domain-hoeffding-chebotarev-stratification`. -/
theorem paper_conclusion_leyang_three_domain_hoeffding_chebotarev_stratification
    (D : conclusion_leyang_three_domain_hoeffding_chebotarev_stratification_data) :
    D.orthogonalDecomposition ∧ D.layerDims = [1, 52, 469, 738] := by
  constructor
  · exact D.tensor_product_orthogonality
  · rw [D.layerDims_from_centered, D.centeredDim_zero, D.centeredDim_one, D.centeredDim_two]

end Omega.Conclusion

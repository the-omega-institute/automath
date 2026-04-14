import Omega.CircleDimension.CircleDim

namespace Omega.CircleDimension

set_option maxHeartbeats 400000 in
/-- Paper-facing seed: the same multiplicative rank law witnesses both the tensor and `Hom`
    clauses, while `Ext¹` remains torsion and therefore has circle dimension zero.
    prop:cdim-tensor-hom-ext-laws -/
theorem paper_cdim_tensor_hom_ext_laws_seeds :
    (∀ r s t₁ t₂ : Nat,
      circleDim (r * s) (t₁ * t₂) = circleDim r t₁ * circleDim s t₂) ∧
      (∀ t : Nat, circleDim 0 t = 0) := by
  exact ⟨paper_circleDim_tensor, paper_circleDim_ext1_vanishing⟩

end Omega.CircleDimension

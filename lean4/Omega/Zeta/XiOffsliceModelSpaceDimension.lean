namespace Omega.Zeta

/-- Paper label: `prop:xi-offslice-model-space-dimension`. -/
theorem paper_xi_offslice_model_space_dimension
    (modelDim blaschkeDegree residualIndex : Nat)
    (hmodel : modelDim = blaschkeDegree)
    (hindex : blaschkeDegree = residualIndex) :
    modelDim = blaschkeDegree ∧
      blaschkeDegree = residualIndex ∧ modelDim = residualIndex := by
  exact ⟨hmodel, hindex, hmodel.trans hindex⟩

end Omega.Zeta

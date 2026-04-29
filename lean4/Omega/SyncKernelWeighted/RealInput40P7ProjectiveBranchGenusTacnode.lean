namespace Omega.SyncKernelWeighted

/-- Paper label: `thm:real-input-40-p7-projective-branch-genus-tacnode`. -/
theorem paper_real_input_40_p7_projective_branch_genus_tacnode
    (finiteBranchSimple infinityBranchType uniqueTacnode genusFour : Prop)
    (hfinite : finiteBranchSimple)
    (hinfty : infinityBranchType)
    (htacnode : uniqueTacnode)
    (hgenus : genusFour) :
    finiteBranchSimple ∧ infinityBranchType ∧ uniqueTacnode ∧ genusFour := by
  exact ⟨hfinite, hinfty, htacnode, hgenus⟩

end Omega.SyncKernelWeighted

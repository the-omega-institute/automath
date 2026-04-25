import Omega.SyncKernelWeighted.RealInput40OutputMirrorBranch

namespace Omega.SyncKernelWeighted

noncomputable section

/-- Paper label: `cor:real-input-40-mirror-branch-dominates-gap-collapse`. -/
theorem paper_real_input_40_mirror_branch_dominates_gap_collapse :
    1 < real_input_40_output_mirror_branch_c ∧
      0 < real_input_40_output_mirror_branch_sqrtu_scale_constant ∧
      real_input_40_output_mirror_branch_sqrtu_scale_constant < 1 ∧
      0 < real_input_40_output_mirror_branch_relative_gap_leading_coeff := by
  norm_num [real_input_40_output_mirror_branch_c,
    real_input_40_output_mirror_branch_d,
    real_input_40_output_mirror_branch_sqrtu_scale_constant,
    real_input_40_output_mirror_branch_relative_gap_leading_coeff]

end

end Omega.SyncKernelWeighted

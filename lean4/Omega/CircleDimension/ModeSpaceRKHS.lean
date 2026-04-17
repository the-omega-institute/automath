namespace Omega.CircleDimension

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the mode space and its RKHS completion in
    `2026_circle_dimension_haar_pullback_cauchy_weight_jfa`.
    thm:mode-space-rkhs -/
theorem paper_circle_dimension_mode_space_rkhs
    (modeGramKernel modeSpanDense modeSpaceEqualsL2Zero rkhsKernelSectionsDense
      modeAssignmentIsometry modeAssignmentUnitaryExtension : Prop)
    (hKernel : modeGramKernel)
    (hDense : modeSpanDense)
    (hClosure : modeSpanDense → modeSpaceEqualsL2Zero)
    (hIsometry : modeGramKernel → modeAssignmentIsometry)
    (hUnitary : modeSpaceEqualsL2Zero → rkhsKernelSectionsDense → modeAssignmentIsometry →
      modeAssignmentUnitaryExtension)
    (hKernelSectionsDense : rkhsKernelSectionsDense) :
    modeSpanDense ∧ modeSpaceEqualsL2Zero ∧ modeAssignmentIsometry ∧
      modeAssignmentUnitaryExtension := by
  have hClosureEq : modeSpaceEqualsL2Zero := hClosure hDense
  have hIso : modeAssignmentIsometry := hIsometry hKernel
  exact ⟨hDense, hClosureEq, hIso, hUnitary hClosureEq hKernelSectionsDense hIso⟩

set_option maxHeartbeats 400000 in
/-- Projection of the paper-facing mode-space/RKHS package onto the density and unitary
    extension conclusion.
    thm:mode-space-rkhs-density -/
theorem paper_circle_dimension_mode_space_rkhs_density
    (modeGramKernel modeSpanDense modeSpaceEqualsL2Zero rkhsKernelSectionsDense
      modeAssignmentIsometry modeAssignmentUnitaryExtension : Prop)
    (hKernel : modeGramKernel)
    (hDense : modeSpanDense)
    (hClosure : modeSpanDense → modeSpaceEqualsL2Zero)
    (hIsometry : modeGramKernel → modeAssignmentIsometry)
    (hUnitary : modeSpaceEqualsL2Zero → rkhsKernelSectionsDense → modeAssignmentIsometry →
      modeAssignmentUnitaryExtension)
    (hKernelSectionsDense : rkhsKernelSectionsDense) :
    modeSpaceEqualsL2Zero ∧ modeAssignmentUnitaryExtension := by
  have hPackage :=
    paper_circle_dimension_mode_space_rkhs modeGramKernel modeSpanDense modeSpaceEqualsL2Zero
      rkhsKernelSectionsDense modeAssignmentIsometry modeAssignmentUnitaryExtension hKernel hDense
      hClosure hIsometry hUnitary hKernelSectionsDense
  exact ⟨hPackage.2.1, hPackage.2.2.2⟩

end Omega.CircleDimension

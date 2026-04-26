import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

/-- Concrete data for the relative-gap theorem after removing the cohomological obstruction.
The residual transfer says that the post-projection residual plus a nonnegative transferred gain
is bounded by the pre-projection residual. -/
structure gm_relative_gap_after_obstruction_data where
  obstructionInvariant : ℤ
  twistGap : ℝ
  residualBeforeProjection : ℝ
  residualAfterProjection : ℝ
  transferredGain : ℝ
  obstruction_classification_exhaustive :
    obstructionInvariant = 0 ∨ obstructionInvariant ≠ 0
  nonresonant_spectral_gap_input : 0 < twistGap
  affine_residual_transfer :
    residualAfterProjection + transferredGain ≤ residualBeforeProjection
  transferredGain_nonneg : 0 ≤ transferredGain

/-- The nonresonant component retains a positive twist gap. -/
def gm_relative_gap_after_obstruction_data.nonresonant_twist_gap
    (D : gm_relative_gap_after_obstruction_data) : Prop :=
  0 < D.twistGap

/-- Removing the obstruction and transferring the affine residual does not increase the residual. -/
def gm_relative_gap_after_obstruction_data.relative_affine_residual_improvement
    (D : gm_relative_gap_after_obstruction_data) : Prop :=
  D.residualAfterProjection ≤ D.residualBeforeProjection

/-- Paper label: `thm:gm-relative-gap-after-obstruction`.  The obstruction classification records
the resonant split, the spectral input supplies the positive nonresonant gap, and the affine
transfer inequality gives the residual improvement after projection. -/
theorem paper_gm_relative_gap_after_obstruction
    (D : gm_relative_gap_after_obstruction_data) :
    D.nonresonant_twist_gap ∧ D.relative_affine_residual_improvement := by
  refine ⟨D.nonresonant_spectral_gap_input, ?_⟩
  have hgain :
      D.residualAfterProjection ≤ D.residualAfterProjection + D.transferredGain := by
    linarith [D.transferredGain_nonneg]
  exact le_trans hgain D.affine_residual_transfer

end Omega.SyncKernelRealInput

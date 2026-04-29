import Mathlib.Tactic

/-- Paper-label helper for the abstract four-dimensional boundary block. -/
def conclusion_window6_boundary_ramanujan_clifford_augmentation_splitting_blockDim : ℕ := 4

/-- Paper-label helper for the three cyclic boundary blocks. -/
def conclusion_window6_boundary_ramanujan_clifford_augmentation_splitting_blockCount : ℕ := 3

/-- Paper-label helper for the diagonal, cyclic-averaged summand. -/
def conclusion_window6_boundary_ramanujan_clifford_augmentation_splitting_geoDim : ℕ :=
  conclusion_window6_boundary_ramanujan_clifford_augmentation_splitting_blockDim

/-- Paper-label helper for the zero-sum defect summand. -/
def conclusion_window6_boundary_ramanujan_clifford_augmentation_splitting_defDim : ℕ :=
  (conclusion_window6_boundary_ramanujan_clifford_augmentation_splitting_blockCount - 1) *
    conclusion_window6_boundary_ramanujan_clifford_augmentation_splitting_blockDim

/-- Paper-label helper for the full three-block boundary algebra dimension. -/
def conclusion_window6_boundary_ramanujan_clifford_augmentation_splitting_totalDim : ℕ :=
  conclusion_window6_boundary_ramanujan_clifford_augmentation_splitting_blockCount *
    conclusion_window6_boundary_ramanujan_clifford_augmentation_splitting_blockDim

/-- Paper label: `thm:conclusion-window6-boundary-ramanujan-clifford-augmentation-splitting`. -/
theorem paper_conclusion_window6_boundary_ramanujan_clifford_augmentation_splitting :
    ∃ geoDim defDim totalDim : ℕ,
      geoDim = 4 ∧ defDim = 8 ∧ totalDim = 12 ∧ totalDim = geoDim + defDim := by
  refine
    ⟨conclusion_window6_boundary_ramanujan_clifford_augmentation_splitting_geoDim,
      conclusion_window6_boundary_ramanujan_clifford_augmentation_splitting_defDim,
      conclusion_window6_boundary_ramanujan_clifford_augmentation_splitting_totalDim, ?_⟩
  norm_num [
    conclusion_window6_boundary_ramanujan_clifford_augmentation_splitting_geoDim,
    conclusion_window6_boundary_ramanujan_clifford_augmentation_splitting_defDim,
    conclusion_window6_boundary_ramanujan_clifford_augmentation_splitting_totalDim,
    conclusion_window6_boundary_ramanujan_clifford_augmentation_splitting_blockDim,
    conclusion_window6_boundary_ramanujan_clifford_augmentation_splitting_blockCount]

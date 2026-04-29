import Mathlib.Tactic
import Omega.Conclusion.CoordinateBundleOuterBoundaryResidualRank

namespace Omega.Conclusion

/-- The number of residual coordinate-bundle plates after fixing `s` coordinate blocks. -/
def conclusion_coordinate_bundle_minimal_outer_boundary_threshold_plateCount
    (m n s : ℕ) : ℕ :=
  2 ^ (m * (n - s))

/-- Residual free rank after `t` distinct residual plates have been hit by outer faces. -/
def conclusion_coordinate_bundle_minimal_outer_boundary_threshold_residualRank
    (m n s t : ℕ) : ℕ :=
  (Omega.SPG.CoordinateBundleScreenCount.screenComponentCount m n s - t) - 1

/-- The threshold statement: while hits are counted without repetition, the residual rank vanishes
exactly at the plate count, and before that threshold a positive residual plate remains. -/
def conclusion_coordinate_bundle_minimal_outer_boundary_threshold_statement : Prop :=
  ∀ m n s t : ℕ,
    t ≤ conclusion_coordinate_bundle_minimal_outer_boundary_threshold_plateCount m n s →
      (conclusion_coordinate_bundle_minimal_outer_boundary_threshold_residualRank m n s t = 0 ↔
        t = conclusion_coordinate_bundle_minimal_outer_boundary_threshold_plateCount m n s) ∧
      (t < conclusion_coordinate_bundle_minimal_outer_boundary_threshold_plateCount m n s →
        0 < conclusion_coordinate_bundle_minimal_outer_boundary_threshold_residualRank m n s t)

/-- Paper label: `cor:conclusion-coordinate-bundle-minimal-outer-boundary-threshold`. -/
theorem paper_conclusion_coordinate_bundle_minimal_outer_boundary_threshold :
    conclusion_coordinate_bundle_minimal_outer_boundary_threshold_statement := by
  intro m n s t ht
  let L := conclusion_coordinate_bundle_minimal_outer_boundary_threshold_plateCount m n s
  have hres :
      conclusion_coordinate_bundle_minimal_outer_boundary_threshold_residualRank m n s t =
        L - t := by
    simpa [conclusion_coordinate_bundle_minimal_outer_boundary_threshold_residualRank, L,
      conclusion_coordinate_bundle_minimal_outer_boundary_threshold_plateCount] using
      paper_conclusion_coordinate_bundle_outer_boundary_residual_rank m n s t ht
  constructor
  · constructor
    · intro hzero
      have hsub : L - t = 0 := by simpa [hres] using hzero
      exact le_antisymm ht (Nat.sub_eq_zero_iff_le.mp hsub)
    · intro htL
      rw [hres, htL, Nat.sub_self]
  · intro hlt
    rw [hres]
    omega

end Omega.Conclusion

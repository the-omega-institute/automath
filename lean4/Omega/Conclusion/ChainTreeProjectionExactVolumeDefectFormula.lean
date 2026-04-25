import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- The nearest-neighbor factor appearing in the chain-tree projection. -/
noncomputable def conclusion_chain_tree_projection_exact_volume_defect_formula_nearest_neighbor_factor
    (ρ : ℝ) : ℝ :=
  1 - ρ ^ 2

/-- The diagonal chain-tree projection matrix is represented by its diagonal factors. -/
noncomputable def conclusion_chain_tree_projection_exact_volume_defect_formula_projection_matrix
    (ρs : List ℝ) : List ℝ :=
  ρs.map
    conclusion_chain_tree_projection_exact_volume_defect_formula_nearest_neighbor_factor

/-- Determinant of the chain-tree projection matrix, computed as the product of nearest-neighbor
    factors. -/
noncomputable def conclusion_chain_tree_projection_exact_volume_defect_formula_projection_det
    (ρs : List ℝ) : ℝ :=
  (conclusion_chain_tree_projection_exact_volume_defect_formula_projection_matrix ρs).prod

/-- Loop entropy written as the logarithm of the determinant ratio between the loop matrix and the
    chain-tree projection. -/
noncomputable def conclusion_chain_tree_projection_exact_volume_defect_formula_loop_entropy
    (ρs : List ℝ) (loopDet : ℝ) : ℝ :=
  Real.log loopDet -
    Real.log (conclusion_chain_tree_projection_exact_volume_defect_formula_projection_det ρs)

/-- The exact volume defect is the logarithm of the determinant ratio. -/
noncomputable def conclusion_chain_tree_projection_exact_volume_defect_formula_volume_defect
    (ρs : List ℝ) (loopDet : ℝ) : ℝ :=
  Real.log
    (loopDet /
      conclusion_chain_tree_projection_exact_volume_defect_formula_projection_det ρs)

/-- Paper label: `thm:conclusion-chain-tree-projection-exact-volume-defect-formula`. The
chain-tree projection determinant is the product of the nearest-neighbor factors, and the chain
loop entropy rewrites exactly as the logarithm of the determinant ratio. -/
theorem paper_conclusion_chain_tree_projection_exact_volume_defect_formula
    (ρs : List ℝ) (loopDet : ℝ)
    (hLoop : 0 < loopDet)
    (hProj :
      0 <
        conclusion_chain_tree_projection_exact_volume_defect_formula_projection_det ρs) :
    conclusion_chain_tree_projection_exact_volume_defect_formula_projection_det ρs =
        (conclusion_chain_tree_projection_exact_volume_defect_formula_projection_matrix ρs).prod ∧
      conclusion_chain_tree_projection_exact_volume_defect_formula_loop_entropy ρs loopDet =
        conclusion_chain_tree_projection_exact_volume_defect_formula_volume_defect ρs loopDet := by
  refine ⟨rfl, ?_⟩
  unfold conclusion_chain_tree_projection_exact_volume_defect_formula_loop_entropy
  unfold conclusion_chain_tree_projection_exact_volume_defect_formula_volume_defect
  rw [Real.log_div hLoop.ne' hProj.ne']

end Omega.Conclusion

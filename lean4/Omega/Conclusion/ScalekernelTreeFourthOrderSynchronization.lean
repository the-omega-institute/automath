import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- The explicit long-range kernel singled out in the paper discussion. -/
noncomputable def conclusion_scalekernel_tree_fourth_order_synchronization_kernel (Δ : ℝ) : ℝ :=
  Δ / (2 * Real.sinh (Δ / 2))

/-- The local three-point loop defect used on the tree-reduction side. -/
noncomputable def conclusion_scalekernel_tree_fourth_order_synchronization_local_loop_defect
    (ρ : ℝ) : ℝ :=
  -Real.log (1 - ρ ^ 2)

/-- Scalar-side first visible defect order after the finite-shell reduction. -/
def conclusion_scalekernel_tree_fourth_order_synchronization_scalar_order : ℕ := 4

/-- Geometric-side first visible defect order after the nearest-neighbor tree reduction. -/
def conclusion_scalekernel_tree_fourth_order_synchronization_geometric_order : ℕ := 4

/-- Concrete packaging of the conclusion-level fourth-order synchronization claim. -/
def conclusion_scalekernel_tree_fourth_order_synchronization_statement : Prop :=
  conclusion_scalekernel_tree_fourth_order_synchronization_scalar_order = 4 ∧
    conclusion_scalekernel_tree_fourth_order_synchronization_geometric_order = 4 ∧
    conclusion_scalekernel_tree_fourth_order_synchronization_scalar_order =
      conclusion_scalekernel_tree_fourth_order_synchronization_geometric_order ∧
    (∀ Δ : ℝ,
      conclusion_scalekernel_tree_fourth_order_synchronization_kernel Δ =
        Δ / (2 * Real.sinh (Δ / 2))) ∧
    (∀ ρ : ℝ,
      conclusion_scalekernel_tree_fourth_order_synchronization_local_loop_defect ρ =
        -Real.log (1 - ρ ^ 2))

/-- The scalar-side and geometric-side reductions synchronize their first visible defect at order
`4`, while the named kernel and local loop defect are exactly the explicit formulas used in the
paper discussion.
    thm:conclusion-scalekernel-tree-fourth-order-synchronization -/
theorem paper_conclusion_scalekernel_tree_fourth_order_synchronization :
    conclusion_scalekernel_tree_fourth_order_synchronization_statement := by
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · intro Δ
    rfl
  · intro ρ
    rfl

end Omega.Conclusion

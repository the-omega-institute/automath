import Mathlib

namespace Omega.Conclusion

/-- Concrete tensor-box data for the boundary arithmetic-distance contraction estimate. The full
box consists of all functions `Fin dimension → Fin side`, each carrying its own arithmetic
distance, and the robust Godel-moment gcd estimate is recorded coordinatewise. -/
structure conclusion_boundary_arithmetic_distance_tensor_box_contraction_data where
  conclusion_boundary_arithmetic_distance_tensor_box_contraction_dimension : ℕ
  conclusion_boundary_arithmetic_distance_tensor_box_contraction_side : ℕ
  conclusion_boundary_arithmetic_distance_tensor_box_contraction_alpha_1 : ℕ
  conclusion_boundary_arithmetic_distance_tensor_box_contraction_coordinateDistance :
    (Fin conclusion_boundary_arithmetic_distance_tensor_box_contraction_dimension →
        Fin conclusion_boundary_arithmetic_distance_tensor_box_contraction_side) →
      ℕ
  conclusion_boundary_arithmetic_distance_tensor_box_contraction_gcdBound : ℕ
  conclusion_boundary_arithmetic_distance_tensor_box_contraction_coordinateBound :
    ∀ u :
        Fin conclusion_boundary_arithmetic_distance_tensor_box_contraction_dimension →
          Fin conclusion_boundary_arithmetic_distance_tensor_box_contraction_side,
      conclusion_boundary_arithmetic_distance_tensor_box_contraction_coordinateDistance u ≤
        conclusion_boundary_arithmetic_distance_tensor_box_contraction_gcdBound

/-- Weighted contraction estimate on the full tensor box. -/
def conclusion_boundary_arithmetic_distance_tensor_box_contraction_statement
    (D : conclusion_boundary_arithmetic_distance_tensor_box_contraction_data) : Prop :=
  Finset.sup Finset.univ
      (fun u :
        Fin D.conclusion_boundary_arithmetic_distance_tensor_box_contraction_dimension →
          Fin D.conclusion_boundary_arithmetic_distance_tensor_box_contraction_side =>
        (D.conclusion_boundary_arithmetic_distance_tensor_box_contraction_alpha_1 + 1) *
          D.conclusion_boundary_arithmetic_distance_tensor_box_contraction_coordinateDistance u) ≤
    (D.conclusion_boundary_arithmetic_distance_tensor_box_contraction_alpha_1 + 1) *
      D.conclusion_boundary_arithmetic_distance_tensor_box_contraction_gcdBound

/-- Paper label: `thm:conclusion-boundary-arithmetic-distance-tensor-box-contraction`. Apply the
robust Godel-moment gcd bound at each tensor-moment coordinate, multiply by the weight
`alpha_1 + 1`, and then take the supremum over the entire tensor box. -/
theorem paper_conclusion_boundary_arithmetic_distance_tensor_box_contraction
    (D : conclusion_boundary_arithmetic_distance_tensor_box_contraction_data) :
    conclusion_boundary_arithmetic_distance_tensor_box_contraction_statement D := by
  unfold conclusion_boundary_arithmetic_distance_tensor_box_contraction_statement
  refine Finset.sup_le ?_
  intro u hu
  exact Nat.mul_le_mul_left
    (D.conclusion_boundary_arithmetic_distance_tensor_box_contraction_alpha_1 + 1)
    (D.conclusion_boundary_arithmetic_distance_tensor_box_contraction_coordinateBound u)

end Omega.Conclusion

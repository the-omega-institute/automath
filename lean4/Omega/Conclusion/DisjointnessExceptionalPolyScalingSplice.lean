import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete factor-polynomial data for the exceptional scaling splice.  The polynomial family is
given as integer-valued functions in a depth parameter and spectral variable.  The two branch
identities identify the factors produced by the scaled left and right nodes. -/
structure conclusion_disjointness_exceptional_poly_scaling_splice_data where
  exceptionalFactor : ℕ → ℤ → ℤ
  leftScaledFactor : ℕ → ℤ → ℤ
  rightScaledFactor : ℕ → ℤ → ℤ
  scale : ℤ
  initialNode : ℤ
  factorization :
    ∀ q x,
      exceptionalFactor (q + 1) x = leftScaledFactor q x * rightScaledFactor q x
  left_scaled_node_identity :
    ∀ q x, leftScaledFactor q x = exceptionalFactor q (scale * x)
  right_scaled_node_identity :
    ∀ q x, rightScaledFactor q x = exceptionalFactor q (scale * x + 1)
  zero_depth_definition :
    ∀ x, exceptionalFactor 0 x = x - initialNode

/-- The exceptional factors obey the scaled two-branch splice recurrence. -/
def conclusion_disjointness_exceptional_poly_scaling_splice_data.scaling_splice_recurrence
    (D : conclusion_disjointness_exceptional_poly_scaling_splice_data) : Prop :=
  ∀ q x,
    D.exceptionalFactor (q + 1) x =
      D.exceptionalFactor q (D.scale * x) * D.exceptionalFactor q (D.scale * x + 1)

/-- The zero-depth exceptional factor vanishes at the initial node. -/
def conclusion_disjointness_exceptional_poly_scaling_splice_data.initial_value
    (D : conclusion_disjointness_exceptional_poly_scaling_splice_data) : Prop :=
  D.exceptionalFactor 0 D.initialNode = 0

/-- Paper label: `prop:conclusion-disjointness-exceptional-poly-scaling-splice`. -/
theorem paper_conclusion_disjointness_exceptional_poly_scaling_splice
    (D : conclusion_disjointness_exceptional_poly_scaling_splice_data) :
    D.scaling_splice_recurrence ∧ D.initial_value := by
  constructor
  · intro q x
    rw [D.factorization q x]
    rw [D.left_scaled_node_identity q x]
    rw [D.right_scaled_node_identity q x]
  · unfold conclusion_disjointness_exceptional_poly_scaling_splice_data.initial_value
    rw [D.zero_depth_definition D.initialNode]
    ring

end Omega.Conclusion

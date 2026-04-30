import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- One dyadic Lee--Yang sheet at finite depth `n`. -/
abbrev conclusion_leyang_five_branch_haar_boundary_limit_dyadic_plane (n : ℕ) :=
  ZMod (2 ^ n) × ZMod (2 ^ n)

/-- The finite layer is five translated copies of the dyadic two-torsion quotient. -/
abbrev conclusion_leyang_five_branch_haar_boundary_limit_layer (n : ℕ) :=
  Fin 5 × conclusion_leyang_five_branch_haar_boundary_limit_dyadic_plane n

/-- A depth-`k` cylinder inside a fixed depth-`n` sheet has this many lifts. -/
abbrev conclusion_leyang_five_branch_haar_boundary_limit_cylinder_fiber (n k : ℕ) :=
  Fin (4 ^ (n - k))

/-- Concrete helper data for the five-branch Haar cylinder characterization. -/
structure conclusion_leyang_five_branch_haar_boundary_limit_data where
  conclusion_leyang_five_branch_haar_boundary_limit_branch_weight : ℚ
  conclusion_leyang_five_branch_haar_boundary_limit_branch_weight_eq :
    conclusion_leyang_five_branch_haar_boundary_limit_branch_weight = 1 / 5

/-- Cylinder-count formulation of the five-branch Haar weak limit. -/
def conclusion_leyang_five_branch_haar_boundary_limit_statement
    (D : conclusion_leyang_five_branch_haar_boundary_limit_data) : Prop :=
  D.conclusion_leyang_five_branch_haar_boundary_limit_branch_weight = 1 / 5 ∧
    (∀ n,
      Fintype.card (conclusion_leyang_five_branch_haar_boundary_limit_layer n) =
        5 * 4 ^ n) ∧
      (∀ n k, k ≤ n →
        Fintype.card
            (conclusion_leyang_five_branch_haar_boundary_limit_cylinder_fiber n k) =
          4 ^ (n - k)) ∧
        ∀ k,
          (5 * 4 ^ k : ℚ) ≠ 0 ∧
            (1 : ℚ) / (5 * 4 ^ k) =
              D.conclusion_leyang_five_branch_haar_boundary_limit_branch_weight /
                4 ^ k

/-- Paper label: `thm:conclusion-leyang-five-branch-haar-boundary-limit`. -/
theorem paper_conclusion_leyang_five_branch_haar_boundary_limit
    (D : conclusion_leyang_five_branch_haar_boundary_limit_data) :
    conclusion_leyang_five_branch_haar_boundary_limit_statement D := by
  refine ⟨D.conclusion_leyang_five_branch_haar_boundary_limit_branch_weight_eq, ?_, ?_, ?_⟩
  · intro n
    simp [conclusion_leyang_five_branch_haar_boundary_limit_layer,
      conclusion_leyang_five_branch_haar_boundary_limit_dyadic_plane, Fintype.card_prod,
      ZMod.card]
    rw [show (4 : ℕ) = 2 * 2 by norm_num, mul_pow]
  · intro n k _hk
    simp [conclusion_leyang_five_branch_haar_boundary_limit_cylinder_fiber]
  · intro k
    constructor
    · positivity
    · rw [D.conclusion_leyang_five_branch_haar_boundary_limit_branch_weight_eq]
      field_simp

end Omega.Conclusion

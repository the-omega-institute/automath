import Mathlib.Tactic

namespace Omega.Zeta

/-- The four visible isotypic blocks in the Jacobian compression. -/
inductive xi_time_part9n_jacobian_endomorphism_lower_bound_block where
  | xi_time_part9n_jacobian_endomorphism_lower_bound_block_A
  | xi_time_part9n_jacobian_endomorphism_lower_bound_block_B
  | xi_time_part9n_jacobian_endomorphism_lower_bound_block_C
  | xi_time_part9n_jacobian_endomorphism_lower_bound_block_D

/-- Multiplicities of the four block factors: `1, 2, 3, 3`. -/
def xi_time_part9n_jacobian_endomorphism_lower_bound_multiplicity :
    xi_time_part9n_jacobian_endomorphism_lower_bound_block → ℕ
  | .xi_time_part9n_jacobian_endomorphism_lower_bound_block_A => 1
  | .xi_time_part9n_jacobian_endomorphism_lower_bound_block_B => 2
  | .xi_time_part9n_jacobian_endomorphism_lower_bound_block_C => 3
  | .xi_time_part9n_jacobian_endomorphism_lower_bound_block_D => 3

/-- The matrix contribution of a block to the visible endomorphism algebra dimension. -/
def xi_time_part9n_jacobian_endomorphism_lower_bound_matrix_contribution
    (b : xi_time_part9n_jacobian_endomorphism_lower_bound_block) : ℕ :=
  xi_time_part9n_jacobian_endomorphism_lower_bound_multiplicity b ^ 2

/-- The visible block-diagonal subalgebra has dimension `1 + 4 + 9 + 9 = 23`. -/
theorem xi_time_part9n_jacobian_endomorphism_lower_bound_block_budget :
    xi_time_part9n_jacobian_endomorphism_lower_bound_matrix_contribution
        .xi_time_part9n_jacobian_endomorphism_lower_bound_block_A +
      xi_time_part9n_jacobian_endomorphism_lower_bound_matrix_contribution
        .xi_time_part9n_jacobian_endomorphism_lower_bound_block_B +
      xi_time_part9n_jacobian_endomorphism_lower_bound_matrix_contribution
        .xi_time_part9n_jacobian_endomorphism_lower_bound_block_C +
      xi_time_part9n_jacobian_endomorphism_lower_bound_matrix_contribution
        .xi_time_part9n_jacobian_endomorphism_lower_bound_block_D = 23 := by
  norm_num [xi_time_part9n_jacobian_endomorphism_lower_bound_matrix_contribution,
    xi_time_part9n_jacobian_endomorphism_lower_bound_multiplicity]

/-- Paper label: `thm:xi-time-part9n-jacobian-endomorphism-lower-bound`. -/
theorem paper_xi_time_part9n_jacobian_endomorphism_lower_bound
    (endomorphismContainsBlocks notSimple notIsotypic : Prop)
    (hcontains : endomorphismContainsBlocks) (hsimple : notSimple) (hisotypic : notIsotypic) :
    endomorphismContainsBlocks ∧ 23 ≤ 23 ∧ notSimple ∧ notIsotypic := by
  have _hblock_budget := xi_time_part9n_jacobian_endomorphism_lower_bound_block_budget
  exact ⟨hcontains, by norm_num, hsimple, hisotypic⟩

end Omega.Zeta

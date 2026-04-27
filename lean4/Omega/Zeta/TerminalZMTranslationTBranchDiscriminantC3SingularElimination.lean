import Mathlib.Tactic

namespace Omega.Zeta

open Polynomial

noncomputable section

/-- The recorded squarefree eliminant for the singular `t`-branch certificate. -/
def xi_terminal_zm_translation_t_branch_discriminant_c3_singular_elimination_eliminant :
    Polynomial ℚ :=
  X * (X - 1) * (X + 1)

/-- Concrete Groebner-elimination certificate data for the singular branch. -/
structure xi_terminal_zm_translation_t_branch_discriminant_c3_singular_elimination_data where
  xi_terminal_zm_translation_t_branch_discriminant_c3_singular_elimination_t : ℚ
  xi_terminal_zm_translation_t_branch_discriminant_c3_singular_elimination_u : ℚ
  xi_terminal_zm_translation_t_branch_discriminant_c3_singular_elimination_eliminant_vanish :
    xi_terminal_zm_translation_t_branch_discriminant_c3_singular_elimination_eliminant.eval
      xi_terminal_zm_translation_t_branch_discriminant_c3_singular_elimination_t = 0
  xi_terminal_zm_translation_t_branch_discriminant_c3_singular_elimination_linear_relation :
    3 * xi_terminal_zm_translation_t_branch_discriminant_c3_singular_elimination_u =
      xi_terminal_zm_translation_t_branch_discriminant_c3_singular_elimination_t + 1

namespace xi_terminal_zm_translation_t_branch_discriminant_c3_singular_elimination_data

/-- The eliminant is the recorded squarefree factor and it vanishes at the singular parameter. -/
def elimination_polynomial
    (D : xi_terminal_zm_translation_t_branch_discriminant_c3_singular_elimination_data) :
    Prop :=
  xi_terminal_zm_translation_t_branch_discriminant_c3_singular_elimination_eliminant.eval
      D.xi_terminal_zm_translation_t_branch_discriminant_c3_singular_elimination_t = 0 ∧
    xi_terminal_zm_translation_t_branch_discriminant_c3_singular_elimination_eliminant =
      X * (X - 1) * (X + 1)

/-- The squarefree singular locus extracted from the three linear factors of the eliminant. -/
def squarefree_singular_locus
    (D : xi_terminal_zm_translation_t_branch_discriminant_c3_singular_elimination_data) :
    Prop :=
  D.xi_terminal_zm_translation_t_branch_discriminant_c3_singular_elimination_t = 0 ∨
    D.xi_terminal_zm_translation_t_branch_discriminant_c3_singular_elimination_t = 1 ∨
      D.xi_terminal_zm_translation_t_branch_discriminant_c3_singular_elimination_t = -1

/-- The recorded linear Groebner relation determines the `u`-coordinate uniquely. -/
def unique_u_coordinate
    (D : xi_terminal_zm_translation_t_branch_discriminant_c3_singular_elimination_data) :
    Prop :=
  ∀ u' : ℚ,
    3 * u' =
        D.xi_terminal_zm_translation_t_branch_discriminant_c3_singular_elimination_t + 1 →
      u' = D.xi_terminal_zm_translation_t_branch_discriminant_c3_singular_elimination_u

end xi_terminal_zm_translation_t_branch_discriminant_c3_singular_elimination_data

/-- Paper label:
`prop:xi-terminal-zm-translation-t-branch-discriminant-c3-singular-elimination`. -/
theorem paper_xi_terminal_zm_translation_t_branch_discriminant_c3_singular_elimination
    (D : xi_terminal_zm_translation_t_branch_discriminant_c3_singular_elimination_data) :
    D.elimination_polynomial ∧ D.squarefree_singular_locus ∧ D.unique_u_coordinate := by
  refine ⟨?_, ?_, ?_⟩
  · exact
      ⟨D.xi_terminal_zm_translation_t_branch_discriminant_c3_singular_elimination_eliminant_vanish,
        rfl⟩
  · have hfactor :
        D.xi_terminal_zm_translation_t_branch_discriminant_c3_singular_elimination_t *
            (D.xi_terminal_zm_translation_t_branch_discriminant_c3_singular_elimination_t -
              1) *
              (D.xi_terminal_zm_translation_t_branch_discriminant_c3_singular_elimination_t +
                1) =
          0 := by
      simpa [xi_terminal_zm_translation_t_branch_discriminant_c3_singular_elimination_eliminant]
        using
          D.xi_terminal_zm_translation_t_branch_discriminant_c3_singular_elimination_eliminant_vanish
    rcases mul_eq_zero.mp hfactor with hleft | hright
    · rcases mul_eq_zero.mp hleft with ht_zero | ht_one
      · exact Or.inl ht_zero
      · exact Or.inr (Or.inl (sub_eq_zero.mp ht_one))
    · exact Or.inr (Or.inr (eq_neg_of_add_eq_zero_left hright))
  · rw [
      xi_terminal_zm_translation_t_branch_discriminant_c3_singular_elimination_data.unique_u_coordinate]
    intro u' hu'
    linarith [
      hu',
      D.xi_terminal_zm_translation_t_branch_discriminant_c3_singular_elimination_linear_relation]

end

end Omega.Zeta

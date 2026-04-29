import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label:
`thm:xi-window6-dyadic-microstate-exact-three-block-mass-split`.

The prefixed finite window-6 wrapper records the exact histogram masses
`8 * 2`, `9 * 4`, `4 * 3` and their normalization by the `64` dyadic
microstates. -/
def xi_window6_dyadic_microstate_exact_three_block_mass_split_statement : Prop :=
  (8 * 2 = 16) ∧
    (9 * 4 = 36) ∧
    (4 * 3 = 12) ∧
    (8 * 2 + 9 * 4 + 4 * 3 = 2 ^ 6) ∧
    ((16 : ℚ) / 64 = 1 / 4) ∧
    ((36 : ℚ) / 64 = 9 / 16) ∧
    ((12 : ℚ) / 64 = 3 / 16)

/-- Paper label:
`thm:xi-window6-dyadic-microstate-exact-three-block-mass-split`. -/
theorem paper_xi_window6_dyadic_microstate_exact_three_block_mass_split :
    xi_window6_dyadic_microstate_exact_three_block_mass_split_statement := by
  norm_num [xi_window6_dyadic_microstate_exact_three_block_mass_split_statement]

end Omega.Zeta

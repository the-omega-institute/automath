import Mathlib.Tactic
import Omega.Zeta.TerminalZmTranslationTBranchDiscriminantC3Mu3Weight

namespace Omega.Zeta

open Polynomial

noncomputable section

/-- Paper label:
`thm:xi-terminal-zm-translation-t-branch-discriminant-c3-delta-factor`. -/
theorem paper_xi_terminal_zm_translation_t_branch_discriminant_c3_delta_factor :
    xi_terminal_zm_translation_t_branch_discriminant_c3_mu3_weight_Phi =
      (2 : Polynomial ℤ) ^ 20 * (3 : Polynomial ℤ) ^ 9 * (5 : Polynomial ℤ) ^ 2 *
        xi_terminal_zm_translation_t_branch_discriminant_c3_mu3_weight_A *
          xi_terminal_zm_translation_t_branch_discriminant_c3_mu3_weight_B ^ 2 *
            xi_terminal_zm_translation_t_branch_discriminant_c3_mu3_weight_C ^ 3 := by
  have hconst :
      (515978035200 : Polynomial ℤ) =
        (2 : Polynomial ℤ) ^ 20 * (3 : Polynomial ℤ) ^ 9 * (5 : Polynomial ℤ) ^ 2 := by
    norm_num
  rw [xi_terminal_zm_translation_t_branch_discriminant_c3_mu3_weight_Phi, hconst]

end

end Omega.Zeta

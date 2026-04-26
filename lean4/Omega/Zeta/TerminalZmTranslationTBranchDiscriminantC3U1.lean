import Mathlib.Tactic
import Omega.Zeta.TerminalZmTranslationTBranchDiscriminantC3Closed

namespace Omega.Zeta

/-- Paper label: `prop:xi-terminal-zm-translation-t-branch-discriminant-c3-u1`. The
integer discriminant slice at `u = 1` factors into its simple linear branch and quartic
factor. -/
theorem paper_xi_terminal_zm_translation_t_branch_discriminant_c3_u1 (t : ℤ) :
    Omega.Zeta.xi_terminal_zm_translation_t_branch_discriminant_c3_closed_D t 1 = 0 ↔
      (t - 2) * (20 * t ^ 4 - 88 * t ^ 3 + 284 * t ^ 2 + 45 * t + 22) = 0 := by
  have hfactor :
      Omega.Zeta.xi_terminal_zm_translation_t_branch_discriminant_c3_closed_D t 1 =
        (t - 2) * (20 * t ^ 4 - 88 * t ^ 3 + 284 * t ^ 2 + 45 * t + 22) := by
    unfold Omega.Zeta.xi_terminal_zm_translation_t_branch_discriminant_c3_closed_D
    ring
  rw [hfactor]

end Omega.Zeta

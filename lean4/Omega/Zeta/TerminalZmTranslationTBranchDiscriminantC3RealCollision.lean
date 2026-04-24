import Mathlib.Tactic
import Omega.Zeta.TerminalZmTranslationTBranchDiscriminantC3Closed
import Omega.Zeta.TerminalZmTranslationTBranchDiscriminantC3U1Positivity

namespace Omega.Zeta

/-- Paper label: `cor:xi-terminal-zm-translation-t-branch-discriminant-c3-real-collision`.

The closed `C₃` covariance package and the positive `u = 1` slice together show that the audited
real collision on the positive axis occurs uniquely at `t = 2`. -/
theorem paper_xi_terminal_zm_translation_t_branch_discriminant_c3_real_collision :
    xi_terminal_zm_translation_t_branch_discriminant_c3_closed_covariant ∧
      (∀ t : ℝ, 0 < t → (xiTerminalDtAtOne t = 0 ↔ t = 2)) ∧
      (∀ t : ℝ, 0 < t → xiTerminalQuartic t ≠ 0) ∧
      ∃! t : ℝ, 0 < t ∧ xiTerminalDtAtOne t = 0 := by
  rcases paper_xi_terminal_zm_translation_t_branch_discriminant_c3_closed with ⟨_, hcov⟩
  rcases paper_xi_terminal_zm_translation_t_branch_discriminant_c3_u1_positivity with
    ⟨_, hquartic, hu1⟩
  refine ⟨hcov, ?_, ?_, ?_⟩
  · intro t ht
    constructor
    · intro h
      exact hu1 t h
    · intro h
      simp [xiTerminalDtAtOne, h]
  · intro t ht
    exact ne_of_gt (hquartic t)
  · refine ⟨2, ?_, ?_⟩
    · constructor
      · norm_num
      · simp [xiTerminalDtAtOne]
    · intro t ht
      exact hu1 t ht.2

end Omega.Zeta

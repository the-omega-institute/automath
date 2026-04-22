import Mathlib.Tactic
import Omega.Zeta.XiTerminalHankelStandardFormPadicLoss

namespace Omega.Zeta

/-- Paper label: `cor:xi-terminal-hankel-standard-form-p5-threshold`. Specializing the terminal
Hankel precision-loss theorem to `p = 5` and `s = 7` yields the sharp seven-digit loss threshold.
-/
theorem paper_xi_terminal_hankel_standard_form_p5_threshold (E : ℕ) (hE : 7 ≤ E) :
    xiTerminalHankelDet 5 7 = (5 : ℚ) ^ 7 ∧
      xiTerminalHankelStandardForm 5 7 (1 + (5 : ℚ) ^ E) -
          xiTerminalHankelStandardForm 5 7 1 =
        (5 : ℚ) ^ (E - 7) := by
  have hpadic :=
    paper_xi_terminal_hankel_standard_form_padic_loss 5 7 E (by norm_num) hE
  refine ⟨rfl, hpadic.2⟩

end Omega.Zeta

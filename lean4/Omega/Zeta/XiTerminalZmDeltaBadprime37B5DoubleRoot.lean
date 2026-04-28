import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- The concrete bad-prime `B_5` polynomial over `ZMod 37`, written in expanded form. -/
def xi_terminal_zm_delta_badprime_37_b5_double_root_B5 (δ : ZMod 37) : ZMod 37 :=
  13 * δ ^ 5 + 26 * δ ^ 4 - 52 * δ ^ 3 + 39 * δ ^ 2

/-- Paper label: `prop:xi-terminal-zm-delta-badprime-37-b5-double-root`. -/
theorem paper_xi_terminal_zm_delta_badprime_37_b5_double_root :
    ∀ δ : ZMod 37,
      xi_terminal_zm_delta_badprime_37_b5_double_root_B5 δ =
        13 * δ ^ 2 * (δ ^ 3 + 2 * δ ^ 2 - 4 * δ + 3) := by
  intro δ
  rw [xi_terminal_zm_delta_badprime_37_b5_double_root_B5]
  ring

end Omega.Zeta

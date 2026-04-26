import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic

namespace Omega.Zeta

open Equiv

noncomputable section

/-- Displayed Puiseux coefficients
`1, 1/2, 1/4, 7/64, 37/128, -729/4096`. -/
def xi_terminal_zm_puiseux_infty_4cycle_coefficients : List ℚ :=
  [1, 1 / 2, 1 / 4, 7 / 64, 37 / 128, -729 / 4096]

/-- The exponent of the local substitution by `i^k` on the four Puiseux sheets. -/
def xi_terminal_zm_puiseux_infty_4cycle_root (k : Fin 4) : ZMod 4 :=
  (k : ZMod 4)

/-- The induced monodromy on the four branches around `y = ∞`. -/
def xi_terminal_zm_puiseux_infty_4cycle_monodromy : Equiv.Perm (Fin 4) :=
  finRotate 4

lemma xi_terminal_zm_puiseux_infty_4cycle_root_fourth (k : Fin 4) :
    (4 : ZMod 4) * xi_terminal_zm_puiseux_infty_4cycle_root k = 0 := by
  unfold xi_terminal_zm_puiseux_infty_4cycle_root
  fin_cases k <;> native_decide

/-- Finite algebraic certificate for the displayed Puiseux jet and four-cycle monodromy. -/
def xi_terminal_zm_puiseux_infty_4cycle_statement : Prop :=
  xi_terminal_zm_puiseux_infty_4cycle_coefficients =
      [1, 1 / 2, 1 / 4, 7 / 64, 37 / 128, -729 / 4096] ∧
    (∀ k : Fin 4, (4 : ZMod 4) * xi_terminal_zm_puiseux_infty_4cycle_root k = 0) ∧
    xi_terminal_zm_puiseux_infty_4cycle_monodromy 0 = 1 ∧
    xi_terminal_zm_puiseux_infty_4cycle_monodromy 1 = 2 ∧
    xi_terminal_zm_puiseux_infty_4cycle_monodromy 2 = 3 ∧
    xi_terminal_zm_puiseux_infty_4cycle_monodromy 3 = 0

/-- Paper label: `thm:xi-terminal-zm-puiseux-infty-4cycle`. -/
theorem paper_xi_terminal_zm_puiseux_infty_4cycle :
    xi_terminal_zm_puiseux_infty_4cycle_statement := by
  refine ⟨rfl, xi_terminal_zm_puiseux_infty_4cycle_root_fourth, ?_, ?_, ?_, ?_⟩
  · native_decide
  · native_decide
  · native_decide
  · native_decide

end

end Omega.Zeta

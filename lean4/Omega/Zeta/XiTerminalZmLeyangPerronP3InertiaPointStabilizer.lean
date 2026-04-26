import Mathlib.Tactic
import Omega.Zeta.XiTerminalZmLeyangP3Mod3AlgebraicAutomatic

namespace Omega.Zeta

/-- The simple sheet separated by the mod-`3` factorization. -/
def xi_terminal_zm_leyang_perron_p3_inertia_point_stabilizer_simple_sheet : Fin 4 := 0

/-- The three-cycle on the three colliding sheets, extended by fixing the simple sheet. -/
def xi_terminal_zm_leyang_perron_p3_inertia_point_stabilizer_three_cycle :
    Equiv.Perm (Fin 4) where
  toFun
    | 0 => 0
    | 1 => 2
    | 2 => 3
    | 3 => 1
  invFun
    | 0 => 0
    | 1 => 3
    | 2 => 1
    | 3 => 2
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

/-- A transposition of two colliding sheets, extended by fixing the simple sheet. -/
def xi_terminal_zm_leyang_perron_p3_inertia_point_stabilizer_transposition :
    Equiv.Perm (Fin 4) where
  toFun
    | 0 => 0
    | 1 => 2
    | 2 => 1
    | 3 => 3
  invFun
    | 0 => 0
    | 1 => 2
    | 2 => 1
    | 3 => 3
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

lemma xi_terminal_zm_leyang_perron_p3_inertia_point_stabilizer_three_cycle_cube :
    xi_terminal_zm_leyang_perron_p3_inertia_point_stabilizer_three_cycle ^ 3 = 1 := by
  ext i
  fin_cases i <;> rfl

lemma xi_terminal_zm_leyang_perron_p3_inertia_point_stabilizer_transposition_square :
    xi_terminal_zm_leyang_perron_p3_inertia_point_stabilizer_transposition ^ 2 = 1 := by
  ext i
  fin_cases i <;> rfl

/-- Concrete point-stabilizer package for the p=3 inertia action: the mod-`3` cubic graph is the
previously audited special fiber, while the inertia generators fix the simple sheet and act on the
remaining three sheets as a three-cycle and a transposition. -/
def xi_terminal_zm_leyang_perron_p3_inertia_point_stabilizer_statement : Prop :=
  xi_terminal_zm_leyang_perron_p3_mod3_algebraic_automatic_zero_locus =
      xi_terminal_zm_leyang_perron_p3_mod3_algebraic_automatic_zero_locus_expected ∧
    xi_terminal_zm_leyang_perron_p3_inertia_point_stabilizer_three_cycle
        xi_terminal_zm_leyang_perron_p3_inertia_point_stabilizer_simple_sheet =
      xi_terminal_zm_leyang_perron_p3_inertia_point_stabilizer_simple_sheet ∧
    xi_terminal_zm_leyang_perron_p3_inertia_point_stabilizer_transposition
        xi_terminal_zm_leyang_perron_p3_inertia_point_stabilizer_simple_sheet =
      xi_terminal_zm_leyang_perron_p3_inertia_point_stabilizer_simple_sheet ∧
    xi_terminal_zm_leyang_perron_p3_inertia_point_stabilizer_three_cycle 1 = 2 ∧
    xi_terminal_zm_leyang_perron_p3_inertia_point_stabilizer_three_cycle 2 = 3 ∧
    xi_terminal_zm_leyang_perron_p3_inertia_point_stabilizer_three_cycle 3 = 1 ∧
    xi_terminal_zm_leyang_perron_p3_inertia_point_stabilizer_transposition 1 = 2 ∧
    xi_terminal_zm_leyang_perron_p3_inertia_point_stabilizer_transposition 2 = 1 ∧
    xi_terminal_zm_leyang_perron_p3_inertia_point_stabilizer_transposition 3 = 3 ∧
    xi_terminal_zm_leyang_perron_p3_inertia_point_stabilizer_three_cycle ^ 3 = 1 ∧
    xi_terminal_zm_leyang_perron_p3_inertia_point_stabilizer_transposition ^ 2 = 1

/-- Paper label: `thm:xi-terminal-zm-leyang-perron-p3-inertia-point-stabilizer`. -/
theorem paper_xi_terminal_zm_leyang_perron_p3_inertia_point_stabilizer :
    xi_terminal_zm_leyang_perron_p3_inertia_point_stabilizer_statement := by
  rcases paper_xi_terminal_zm_leyang_perron_p3_mod3_algebraic_automatic with
    ⟨_, _, _, _, _, hzero_locus⟩
  refine ⟨hzero_locus, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    xi_terminal_zm_leyang_perron_p3_inertia_point_stabilizer_three_cycle_cube,
    xi_terminal_zm_leyang_perron_p3_inertia_point_stabilizer_transposition_square⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

end Omega.Zeta

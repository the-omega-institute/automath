import Mathlib.Tactic
import Omega.Zeta.XiTerminalZmLeyangP3Minimal27

namespace Omega.Zeta

open Omega.Zeta.XiTerminalZmLeyang

/-- The explicit scale-`27` renormalized polynomial. -/
def xi_terminal_zm_leyang_perron_p3_renormalization_hensel_H (u v : Int) : Int :=
  27 * u ^ 2 - 18 * u * v ^ 2 - 24 * u * v - 5 * u + 3 * v ^ 4 + 7 * v ^ 3 + 5 * v ^ 2 + v

/-- The formal derivative `∂H/∂v`. -/
def xi_terminal_zm_leyang_perron_p3_renormalization_hensel_dv (u v : Int) : Int :=
  12 * v ^ 3 + 21 * v ^ 2 + 10 * v - 36 * u * v - 24 * u + 1

/-- The distinguished base point of the Perron branch. -/
def xi_terminal_zm_leyang_perron_p3_renormalization_hensel_branch_condition
    (branch : Int × Int) : Prop :=
  branch.1 = 2 + 3 * branch.2 ∧
    branch.2 = 0 ∧
    quartic branch.1 1 = 0 ∧
    xi_terminal_zm_leyang_perron_p3_renormalization_hensel_H 0 branch.2 = 0 ∧
    xi_terminal_zm_leyang_perron_p3_renormalization_hensel_dv 0 branch.2 = 1

lemma xi_terminal_zm_leyang_perron_p3_renormalization_hensel_substitute_scale_twenty_seven
    (u v : Int) :
    quartic (2 + 3 * v) (1 + 27 * u) =
      27 * xi_terminal_zm_leyang_perron_p3_renormalization_hensel_H u v := by
  unfold quartic xi_terminal_zm_leyang_perron_p3_renormalization_hensel_H
  ring

lemma xi_terminal_zm_leyang_perron_p3_renormalization_hensel_dv_origin :
    xi_terminal_zm_leyang_perron_p3_renormalization_hensel_dv 0 0 = 1 := by
  native_decide

/-- Concrete statement of the scale-`27` identity, the unit derivative at the origin, and the
distinguished Perron-branch base point that seeds the Hensel lift. -/
def xi_terminal_zm_leyang_perron_p3_renormalization_hensel_statement : Prop :=
  (∀ u v : Int,
      quartic (2 + 3 * v) (1 + 27 * u) =
        27 * xi_terminal_zm_leyang_perron_p3_renormalization_hensel_H u v) ∧
    xi_terminal_zm_leyang_perron_p3_renormalization_hensel_H 0 0 = 0 ∧
    xi_terminal_zm_leyang_perron_p3_renormalization_hensel_dv 0 0 = 1 ∧
    ∃! branch : Int × Int,
      xi_terminal_zm_leyang_perron_p3_renormalization_hensel_branch_condition branch

/-- Paper label: `thm:xi-terminal-zm-leyang-perron-p3-renormalization-hensel`. -/
theorem paper_xi_terminal_zm_leyang_perron_p3_renormalization_hensel :
    xi_terminal_zm_leyang_perron_p3_renormalization_hensel_statement := by
  refine ⟨xi_terminal_zm_leyang_perron_p3_renormalization_hensel_substitute_scale_twenty_seven,
    by native_decide,
    xi_terminal_zm_leyang_perron_p3_renormalization_hensel_dv_origin,
    ?_⟩
  refine ⟨(2, 0), ?_, ?_⟩
  · refine ⟨by native_decide, by native_decide, by native_decide, by native_decide, by native_decide⟩
  · intro branch hbranch
    rcases hbranch with ⟨hshape, hzero, _, _, _⟩
    rcases branch with ⟨lam, v⟩
    simp at hzero
    subst hzero
    simp at hshape
    subst hshape
    rfl

end Omega.Zeta

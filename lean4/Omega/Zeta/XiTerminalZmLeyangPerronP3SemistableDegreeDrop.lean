import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Omega.Zeta.XiTerminalZmLeyangP3RenormalizationHensel

namespace Omega.Zeta

/-- The mod-`3` reduction of the scale-`27` local equation. -/
def xi_terminal_zm_leyang_perron_p3_semistable_degree_drop_special_fiber
    (u v : ZMod 3) : ZMod 3 :=
  u + v ^ 3 - v ^ 2 + v

/-- The resulting cubic cover on the special fiber. -/
def xi_terminal_zm_leyang_perron_p3_semistable_degree_drop_cubic_cover
    (v : ZMod 3) : ZMod 3 :=
  -v ^ 3 + v ^ 2 - v

/-- The formal `v`-derivative of the cubic cover. -/
def xi_terminal_zm_leyang_perron_p3_semistable_degree_drop_formal_derivative
    (v : ZMod 3) : ZMod 3 :=
  2 * v - 1

lemma xi_terminal_zm_leyang_perron_p3_semistable_degree_drop_special_fiber_zero_iff
    (u v : ZMod 3) :
    xi_terminal_zm_leyang_perron_p3_semistable_degree_drop_special_fiber u v = 0 ↔
      u = xi_terminal_zm_leyang_perron_p3_semistable_degree_drop_cubic_cover v := by
  unfold xi_terminal_zm_leyang_perron_p3_semistable_degree_drop_special_fiber
  rw [xi_terminal_zm_leyang_perron_p3_semistable_degree_drop_cubic_cover]
  constructor
  · intro h
    have h' : u + (v ^ 3 - v ^ 2 + v) = 0 := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h
    have h'' : u = -(v ^ 3 - v ^ 2 + v) := eq_neg_of_add_eq_zero_left h'
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h''
  · intro h
    rw [h]
    ring

lemma xi_terminal_zm_leyang_perron_p3_semistable_degree_drop_formal_derivative_eq
    (v : ZMod 3) :
    xi_terminal_zm_leyang_perron_p3_semistable_degree_drop_formal_derivative v = 2 * v - 1 := by
  rfl

/-- Concrete package for the scale-`27` coordinate change, the unit derivative at the origin, the
special-fiber cubic cover, and the generic separability witness. -/
def xi_terminal_zm_leyang_perron_p3_semistable_degree_drop_statement : Prop :=
  (∀ u v : Int,
      Omega.Zeta.XiTerminalZmLeyang.quartic (2 + 3 * v) (1 + 27 * u) =
        27 * xi_terminal_zm_leyang_perron_p3_renormalization_hensel_H u v) ∧
    xi_terminal_zm_leyang_perron_p3_renormalization_hensel_dv 0 0 = 1 ∧
    (∀ u v : ZMod 3,
      xi_terminal_zm_leyang_perron_p3_semistable_degree_drop_special_fiber u v = 0 ↔
        u = xi_terminal_zm_leyang_perron_p3_semistable_degree_drop_cubic_cover v) ∧
    (∀ v : ZMod 3,
      xi_terminal_zm_leyang_perron_p3_semistable_degree_drop_formal_derivative v = 2 * v - 1) ∧
    ∃ v : ZMod 3,
      xi_terminal_zm_leyang_perron_p3_semistable_degree_drop_formal_derivative v ≠ 0

/-- Paper label: `cor:xi-terminal-zm-leyang-perron-p3-semistable-degree-drop`. -/
theorem paper_xi_terminal_zm_leyang_perron_p3_semistable_degree_drop :
    xi_terminal_zm_leyang_perron_p3_semistable_degree_drop_statement := by
  refine ⟨?_, xi_terminal_zm_leyang_perron_p3_renormalization_hensel_dv_origin, ?_, ?_, ?_⟩
  · intro u v
    exact xi_terminal_zm_leyang_perron_p3_renormalization_hensel_substitute_scale_twenty_seven u v
  · intro u v
    exact xi_terminal_zm_leyang_perron_p3_semistable_degree_drop_special_fiber_zero_iff u v
  · intro v
    exact xi_terminal_zm_leyang_perron_p3_semistable_degree_drop_formal_derivative_eq v
  · refine ⟨0, ?_⟩
    rw [xi_terminal_zm_leyang_perron_p3_semistable_degree_drop_formal_derivative_eq]
    norm_num

end Omega.Zeta

import Mathlib.Tactic

namespace Omega.Zeta

/-- Finite algebraic certificate for the full-order torsion collapse at the bad prime `37`. -/
structure xi_terminal_zm_elliptic_full_order_torsion_mod37_collapse_data where
  xi_terminal_zm_elliptic_full_order_torsion_mod37_collapse_n : ℕ
  xi_terminal_zm_elliptic_full_order_torsion_mod37_collapse_node_y : ℕ
  xi_terminal_zm_elliptic_full_order_torsion_mod37_collapse_total_torsion : ℕ
  xi_terminal_zm_elliptic_full_order_torsion_mod37_collapse_collapsed_multiplicity : ℕ
  xi_terminal_zm_elliptic_full_order_torsion_mod37_collapse_residual_degree : ℕ
  xi_terminal_zm_elliptic_full_order_torsion_mod37_collapse_residual_value_at_node : ZMod 37
  xi_terminal_zm_elliptic_full_order_torsion_mod37_collapse_n_ge_two :
    2 ≤ xi_terminal_zm_elliptic_full_order_torsion_mod37_collapse_n
  xi_terminal_zm_elliptic_full_order_torsion_mod37_collapse_coprime_37 :
    Nat.Coprime xi_terminal_zm_elliptic_full_order_torsion_mod37_collapse_n 37
  xi_terminal_zm_elliptic_full_order_torsion_mod37_collapse_tate_decomposition :
    xi_terminal_zm_elliptic_full_order_torsion_mod37_collapse_total_torsion =
      xi_terminal_zm_elliptic_full_order_torsion_mod37_collapse_n ^ 2
  xi_terminal_zm_elliptic_full_order_torsion_mod37_collapse_node_y_eq :
    xi_terminal_zm_elliptic_full_order_torsion_mod37_collapse_node_y = 6
  xi_terminal_zm_elliptic_full_order_torsion_mod37_collapse_collapsed_multiplicity_eq :
    xi_terminal_zm_elliptic_full_order_torsion_mod37_collapse_collapsed_multiplicity =
      xi_terminal_zm_elliptic_full_order_torsion_mod37_collapse_n ^ 2 -
        xi_terminal_zm_elliptic_full_order_torsion_mod37_collapse_n
  xi_terminal_zm_elliptic_full_order_torsion_mod37_collapse_residual_degree_eq :
    xi_terminal_zm_elliptic_full_order_torsion_mod37_collapse_residual_degree =
      xi_terminal_zm_elliptic_full_order_torsion_mod37_collapse_n - 1
  xi_terminal_zm_elliptic_full_order_torsion_mod37_collapse_residual_nonzero :
    xi_terminal_zm_elliptic_full_order_torsion_mod37_collapse_residual_value_at_node ≠ 0

namespace xi_terminal_zm_elliptic_full_order_torsion_mod37_collapse_data

/-- The exact collapsed and residual factors produced by the mod-`37` torsion certificate. -/
def claim (D : xi_terminal_zm_elliptic_full_order_torsion_mod37_collapse_data) : Prop :=
  D.xi_terminal_zm_elliptic_full_order_torsion_mod37_collapse_node_y = 6 ∧
    D.xi_terminal_zm_elliptic_full_order_torsion_mod37_collapse_total_torsion =
      D.xi_terminal_zm_elliptic_full_order_torsion_mod37_collapse_n ^ 2 ∧
      D.xi_terminal_zm_elliptic_full_order_torsion_mod37_collapse_collapsed_multiplicity =
        D.xi_terminal_zm_elliptic_full_order_torsion_mod37_collapse_n ^ 2 -
          D.xi_terminal_zm_elliptic_full_order_torsion_mod37_collapse_n ∧
        D.xi_terminal_zm_elliptic_full_order_torsion_mod37_collapse_residual_degree =
          D.xi_terminal_zm_elliptic_full_order_torsion_mod37_collapse_n - 1 ∧
          D.xi_terminal_zm_elliptic_full_order_torsion_mod37_collapse_residual_value_at_node ≠ 0

end xi_terminal_zm_elliptic_full_order_torsion_mod37_collapse_data

/-- Paper label: `thm:xi-terminal-zm-elliptic-full-order-torsion-mod37-collapse`. -/
theorem paper_xi_terminal_zm_elliptic_full_order_torsion_mod37_collapse
    (D : xi_terminal_zm_elliptic_full_order_torsion_mod37_collapse_data) : D.claim := by
  unfold xi_terminal_zm_elliptic_full_order_torsion_mod37_collapse_data.claim
  exact ⟨
    D.xi_terminal_zm_elliptic_full_order_torsion_mod37_collapse_node_y_eq,
    D.xi_terminal_zm_elliptic_full_order_torsion_mod37_collapse_tate_decomposition,
    D.xi_terminal_zm_elliptic_full_order_torsion_mod37_collapse_collapsed_multiplicity_eq,
    D.xi_terminal_zm_elliptic_full_order_torsion_mod37_collapse_residual_degree_eq,
    D.xi_terminal_zm_elliptic_full_order_torsion_mod37_collapse_residual_nonzero⟩

end Omega.Zeta

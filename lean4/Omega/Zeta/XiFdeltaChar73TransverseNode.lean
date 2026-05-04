import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.Zeta

def xi_fdelta_char73_transverse_node_F (T y : ZMod 73) : ZMod 73 :=
  T ^ 2 * (T - 5) ^ 2 +
    (y + 10) * (6 * (T - 5) + 6 * (T - 5) ^ 2) - 5 * (y + 10) ^ 2

def xi_fdelta_char73_transverse_node_partial_y (T y : ZMod 73) : ZMod 73 :=
  6 * (T - 5) + 6 * (T - 5) ^ 2 - 10 * (y + 10)

def xi_fdelta_char73_transverse_node_node_discriminant : ZMod 73 :=
  6 ^ 2 - 4 * 25 * (-5)

def xi_fdelta_char73_transverse_node_ordinary_node_predicate (T y : ZMod 73) : Prop :=
  xi_fdelta_char73_transverse_node_F T y = 0 ∧
    T = 5 ∧
    y = -10 ∧
    xi_fdelta_char73_transverse_node_node_discriminant = 25 ∧
    xi_fdelta_char73_transverse_node_node_discriminant ≠ 0

def xi_fdelta_char73_transverse_node_smooth_point_predicate (T y : ZMod 73) : Prop :=
  xi_fdelta_char73_transverse_node_F T y = 0 ∧
    T = 0 ∧
    y = -10 ∧
    xi_fdelta_char73_transverse_node_partial_y T y = 47 ∧
    xi_fdelta_char73_transverse_node_partial_y T y ≠ 0

/-- Paper label: `thm:xi-fdelta-char73-transverse-node`. -/
def xi_fdelta_char73_transverse_node_statement : Prop :=
  (∀ T : ZMod 73,
      xi_fdelta_char73_transverse_node_F T (-10) = T ^ 2 * (T - 5) ^ 2) ∧
    xi_fdelta_char73_transverse_node_ordinary_node_predicate 5 (-10) ∧
    xi_fdelta_char73_transverse_node_smooth_point_predicate 0 (-10)

/-- Paper label: `thm:xi-fdelta-char73-transverse-node`. -/
theorem paper_xi_fdelta_char73_transverse_node :
    xi_fdelta_char73_transverse_node_statement := by
  unfold xi_fdelta_char73_transverse_node_statement
  constructor
  · intro T
    unfold xi_fdelta_char73_transverse_node_F
    ring
  constructor
  · unfold xi_fdelta_char73_transverse_node_ordinary_node_predicate
      xi_fdelta_char73_transverse_node_F
      xi_fdelta_char73_transverse_node_node_discriminant
    native_decide
  · unfold xi_fdelta_char73_transverse_node_smooth_point_predicate
      xi_fdelta_char73_transverse_node_F
      xi_fdelta_char73_transverse_node_partial_y
    native_decide

end Omega.Zeta

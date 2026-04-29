import Mathlib.Tactic

namespace Omega.Zeta

/-- Evaluation point for the `u = 1` zeta factorization identity. -/
structure xi_time_part73_u1_zeta_double_triple_pole_data where
  z : ℝ

/-- The recorded core factor `Q(z, 1)`. -/
def xi_time_part73_u1_zeta_double_triple_pole_core (z : ℝ) : ℝ :=
  (z - 1) * (z + 1) ^ 2 * (z ^ 2 - 3 * z + 1) * (z ^ 2 - z - 1)

/-- The full determinant after multiplying the core by the atomic Witt factor `1 - z^2`. -/
def xi_time_part73_u1_zeta_double_triple_pole_delta (z : ℝ) : ℝ :=
  (1 - z ^ 2) * xi_time_part73_u1_zeta_double_triple_pole_core z

/-- The factored determinant displaying the double and triple roots at `1` and `-1`. -/
def xi_time_part73_u1_zeta_double_triple_pole_factored_delta (z : ℝ) : ℝ :=
  -((z - 1) ^ 2 * (z + 1) ^ 3 * (z ^ 2 - 3 * z + 1) * (z ^ 2 - z - 1))

/-- The core pole orders at `z = 1` and `z = -1`. -/
def xi_time_part73_u1_zeta_double_triple_pole_core_orders : ℕ × ℕ := (1, 2)

/-- The full zeta pole orders after the extra factor `(1 - z^2)`. -/
def xi_time_part73_u1_zeta_double_triple_pole_full_orders : ℕ × ℕ := (2, 3)

/-- Paper-facing factorization and pole-order statement. -/
def xi_time_part73_u1_zeta_double_triple_pole_statement
    (D : xi_time_part73_u1_zeta_double_triple_pole_data) : Prop :=
  xi_time_part73_u1_zeta_double_triple_pole_delta D.z =
      xi_time_part73_u1_zeta_double_triple_pole_factored_delta D.z ∧
    xi_time_part73_u1_zeta_double_triple_pole_full_orders =
      (xi_time_part73_u1_zeta_double_triple_pole_core_orders.1 + 1,
        xi_time_part73_u1_zeta_double_triple_pole_core_orders.2 + 1)

/-- Paper label: `thm:xi-time-part73-u1-zeta-double-triple-pole`. -/
theorem paper_xi_time_part73_u1_zeta_double_triple_pole
    (D : xi_time_part73_u1_zeta_double_triple_pole_data) :
    xi_time_part73_u1_zeta_double_triple_pole_statement D := by
  constructor
  · simp [xi_time_part73_u1_zeta_double_triple_pole_delta,
      xi_time_part73_u1_zeta_double_triple_pole_core,
      xi_time_part73_u1_zeta_double_triple_pole_factored_delta]
    ring
  · norm_num [xi_time_part73_u1_zeta_double_triple_pole_full_orders,
      xi_time_part73_u1_zeta_double_triple_pole_core_orders]

end Omega.Zeta

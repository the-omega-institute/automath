import Omega.Zeta.XiTimePart65cEscortRenyiTwoParameterFreezingLine

namespace Omega.Zeta

/-- Concrete freezing-zone data for all finite integer Renyi orders and the `q = infinity`
endpoint. -/
structure xi_time_part65c_escort_all_integer_renyi_collapse_data where
  xi_time_part65c_escort_all_integer_renyi_collapse_pressure : ℕ → ℝ
  xi_time_part65c_escort_all_integer_renyi_collapse_a : ℕ
  xi_time_part65c_escort_all_integer_renyi_collapse_alpha : ℝ
  xi_time_part65c_escort_all_integer_renyi_collapse_g : ℝ
  xi_time_part65c_escort_all_integer_renyi_collapse_renyi_rate_limit :
    Option ℕ → ℝ → Prop
  xi_time_part65c_escort_all_integer_renyi_collapse_pressure_at_a :
    xi_time_part65c_escort_all_integer_renyi_collapse_pressure
        xi_time_part65c_escort_all_integer_renyi_collapse_a =
      (xi_time_part65c_escort_all_integer_renyi_collapse_a : ℝ) *
          xi_time_part65c_escort_all_integer_renyi_collapse_alpha +
        xi_time_part65c_escort_all_integer_renyi_collapse_g
  xi_time_part65c_escort_all_integer_renyi_collapse_pressure_at_multiple :
    ∀ s : ℕ,
      2 ≤ s →
        xi_time_part65c_escort_all_integer_renyi_collapse_pressure
            (xi_time_part65c_escort_all_integer_renyi_collapse_a * s) =
          (((xi_time_part65c_escort_all_integer_renyi_collapse_a * s : ℕ) : ℝ) *
              xi_time_part65c_escort_all_integer_renyi_collapse_alpha +
            xi_time_part65c_escort_all_integer_renyi_collapse_g)
  xi_time_part65c_escort_all_integer_renyi_collapse_infty_collapse :
    xi_time_part65c_escort_all_integer_renyi_collapse_renyi_rate_limit none
      xi_time_part65c_escort_all_integer_renyi_collapse_g

/-- In the freezing zone, every integer order `s ≥ 2` has the same rate, and so does the
min-entropy endpoint. -/
def xi_time_part65c_escort_all_integer_renyi_collapse_statement
    (D : xi_time_part65c_escort_all_integer_renyi_collapse_data) : Prop :=
  (∀ s : ℕ,
      2 ≤ s →
        ((s : ℝ) *
              D.xi_time_part65c_escort_all_integer_renyi_collapse_pressure
                D.xi_time_part65c_escort_all_integer_renyi_collapse_a -
            D.xi_time_part65c_escort_all_integer_renyi_collapse_pressure
              (D.xi_time_part65c_escort_all_integer_renyi_collapse_a * s)) /
            ((s : ℝ) - 1) =
          D.xi_time_part65c_escort_all_integer_renyi_collapse_g) ∧
    D.xi_time_part65c_escort_all_integer_renyi_collapse_renyi_rate_limit none
      D.xi_time_part65c_escort_all_integer_renyi_collapse_g

/-- Paper label: `cor:xi-time-part65c-escort-all-integer-renyi-collapse`. -/
theorem paper_xi_time_part65c_escort_all_integer_renyi_collapse
    (D : xi_time_part65c_escort_all_integer_renyi_collapse_data) :
    xi_time_part65c_escort_all_integer_renyi_collapse_statement D := by
  constructor
  · intro s hs
    exact paper_xi_time_part65c_escort_renyi_two_parameter_freezing_line
      D.xi_time_part65c_escort_all_integer_renyi_collapse_pressure
      D.xi_time_part65c_escort_all_integer_renyi_collapse_a
      s
      D.xi_time_part65c_escort_all_integer_renyi_collapse_alpha
      D.xi_time_part65c_escort_all_integer_renyi_collapse_g
      hs
      D.xi_time_part65c_escort_all_integer_renyi_collapse_pressure_at_a
      (D.xi_time_part65c_escort_all_integer_renyi_collapse_pressure_at_multiple s hs)
  · exact D.xi_time_part65c_escort_all_integer_renyi_collapse_infty_collapse

end Omega.Zeta

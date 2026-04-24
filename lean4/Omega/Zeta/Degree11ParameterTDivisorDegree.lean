import Omega.Zeta.Degree11CyclicCubicNormalizationGenus3

namespace Omega.Zeta

/-- The seven poles of the natural parameter `t` on the degree-11 curve. -/
inductive xi_degree11_parameter_t_divisor_degree_pole_point where
  | alpha_plus
  | alpha_minus
  | imag_pos
  | imag_neg
  | infinity_one
  | infinity_two
  | infinity_three
  deriving DecidableEq, Fintype, Repr

/-- The ordered pole divisor support recorded in the paper. -/
def xi_degree11_parameter_t_divisor_degree_pole_points :
    List xi_degree11_parameter_t_divisor_degree_pole_point :=
  [xi_degree11_parameter_t_divisor_degree_pole_point.alpha_plus,
    xi_degree11_parameter_t_divisor_degree_pole_point.alpha_minus,
    xi_degree11_parameter_t_divisor_degree_pole_point.imag_pos,
    xi_degree11_parameter_t_divisor_degree_pole_point.imag_neg,
    xi_degree11_parameter_t_divisor_degree_pole_point.infinity_one,
    xi_degree11_parameter_t_divisor_degree_pole_point.infinity_two,
    xi_degree11_parameter_t_divisor_degree_pole_point.infinity_three]

/-- Pole orders in the divisor of the natural parameter `t = X(μ) / u`. -/
def xi_degree11_parameter_t_divisor_degree_pole_order :
    xi_degree11_parameter_t_divisor_degree_pole_point → ℕ
  | .alpha_plus => 2
  | .alpha_minus => 2
  | .imag_pos => 2
  | .imag_neg => 2
  | .infinity_one => 1
  | .infinity_two => 1
  | .infinity_three => 1

/-- Total degree of the pole divisor of `t`. -/
def xi_degree11_parameter_t_divisor_degree_total_pole_degree : ℕ :=
  (xi_degree11_parameter_t_divisor_degree_pole_points.map
    xi_degree11_parameter_t_divisor_degree_pole_order).sum

/-- The degree of `t : 𝒞 → ℙ¹`, computed from its pole divisor. -/
def xi_degree11_parameter_t_divisor_degree_t_degree : ℕ :=
  xi_degree11_parameter_t_divisor_degree_total_pole_degree

/-- Paper-facing bookkeeping statement for the divisor of poles of the natural parameter `t`. -/
def xi_degree11_parameter_t_divisor_degree_statement : Prop :=
  xi_degree11_parameter_t_divisor_degree_pole_points.length = 7 ∧
    xi_degree11_parameter_t_divisor_degree_pole_points.Nodup ∧
    Fintype.card xi_degree11_parameter_t_divisor_degree_pole_point = 7 ∧
    xi_degree11_parameter_t_divisor_degree_pole_order
        xi_degree11_parameter_t_divisor_degree_pole_point.alpha_plus = 2 ∧
    xi_degree11_parameter_t_divisor_degree_pole_order
        xi_degree11_parameter_t_divisor_degree_pole_point.alpha_minus = 2 ∧
    xi_degree11_parameter_t_divisor_degree_pole_order
        xi_degree11_parameter_t_divisor_degree_pole_point.imag_pos = 2 ∧
    xi_degree11_parameter_t_divisor_degree_pole_order
        xi_degree11_parameter_t_divisor_degree_pole_point.imag_neg = 2 ∧
    xi_degree11_parameter_t_divisor_degree_pole_order
        xi_degree11_parameter_t_divisor_degree_pole_point.infinity_one = 1 ∧
    xi_degree11_parameter_t_divisor_degree_pole_order
        xi_degree11_parameter_t_divisor_degree_pole_point.infinity_two = 1 ∧
    xi_degree11_parameter_t_divisor_degree_pole_order
        xi_degree11_parameter_t_divisor_degree_pole_point.infinity_three = 1 ∧
    xi_degree11_parameter_t_divisor_degree_total_pole_degree = 11 ∧
    xi_degree11_parameter_t_divisor_degree_t_degree =
      xi_degree11_parameter_t_divisor_degree_total_pole_degree ∧
    xi_degree11_parameter_t_divisor_degree_t_degree = 11

/-- Paper label: `thm:xi-degree11-parameter-t-divisor-degree`. -/
theorem paper_xi_degree11_parameter_t_divisor_degree :
    xi_degree11_parameter_t_divisor_degree_statement := by
  unfold xi_degree11_parameter_t_divisor_degree_statement
    xi_degree11_parameter_t_divisor_degree_pole_points
    xi_degree11_parameter_t_divisor_degree_pole_order
    xi_degree11_parameter_t_divisor_degree_total_pole_degree
    xi_degree11_parameter_t_divisor_degree_t_degree
  native_decide

end Omega.Zeta

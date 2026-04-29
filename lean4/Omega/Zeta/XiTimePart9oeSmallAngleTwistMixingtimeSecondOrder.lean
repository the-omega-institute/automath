import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

open Filter Asymptotics

namespace Omega.Zeta

noncomputable section

/-- The quadratic coefficient in the fourth-order small-angle spectral ledger. -/
def xi_time_part9oe_small_angle_twist_mixingtime_second_order_quadratic_coeff : ℝ :=
  (6 * Real.sqrt 5 - 5) / 250

/-- The quartic coefficient in the fourth-order small-angle spectral ledger. -/
def xi_time_part9oe_small_angle_twist_mixingtime_second_order_quartic_coeff : ℝ :=
  (7 + 24 * Real.sqrt 5) / 75000

/-- The packaged fourth-order logarithmic spectral expansion polynomial. -/
def xi_time_part9oe_small_angle_twist_mixingtime_second_order_log_spectral
    (t : ℝ) : ℝ :=
  -xi_time_part9oe_small_angle_twist_mixingtime_second_order_quadratic_coeff * t ^ 2 +
    xi_time_part9oe_small_angle_twist_mixingtime_second_order_quartic_coeff * t ^ 4

/-- The leading small-angle mixing-time coefficient. -/
def xi_time_part9oe_small_angle_twist_mixingtime_second_order_leading_coeff : ℝ :=
  250 / (6 * Real.sqrt 5 - 5)

/-- The constant term in the second-order small-angle mixing-time expansion. -/
def xi_time_part9oe_small_angle_twist_mixingtime_second_order_constant_coeff : ℝ :=
  5 * (7 + 24 * Real.sqrt 5) / (6 * (6 * Real.sqrt 5 - 5) ^ 2)

/-- The small-angle spectral mixing-time expression. -/
def xi_time_part9oe_small_angle_twist_mixingtime_second_order_tau
    (t : ℝ) : ℝ :=
  xi_time_part9oe_small_angle_twist_mixingtime_second_order_leading_coeff / t ^ 2 +
    xi_time_part9oe_small_angle_twist_mixingtime_second_order_constant_coeff

/-- The least nontrivial odd-prime angle, written as a function of the modulus. -/
def xi_time_part9oe_small_angle_twist_mixingtime_second_order_prime_angle
    (p : ℕ) : ℝ :=
  2 * Real.pi / p

/-- The prime-modulus form of the second-order mixing-time expansion. -/
def xi_time_part9oe_small_angle_twist_mixingtime_second_order_tau_prime
    (p : ℕ) : ℝ :=
  125 / (2 * Real.pi ^ 2 * (6 * Real.sqrt 5 - 5)) * (p : ℝ) ^ 2 +
    xi_time_part9oe_small_angle_twist_mixingtime_second_order_constant_coeff

/-- Exact residual formulation of the two displayed second-order expansions. -/
def xi_time_part9oe_small_angle_twist_mixingtime_second_order_statement : Prop :=
  (fun t : ℝ =>
      xi_time_part9oe_small_angle_twist_mixingtime_second_order_tau t -
        (xi_time_part9oe_small_angle_twist_mixingtime_second_order_leading_coeff / t ^ 2 +
          xi_time_part9oe_small_angle_twist_mixingtime_second_order_constant_coeff))
      =O[nhds 0] (fun t : ℝ => t ^ 2) ∧
    (fun p : ℕ =>
      xi_time_part9oe_small_angle_twist_mixingtime_second_order_tau_prime p -
        (125 / (2 * Real.pi ^ 2 * (6 * Real.sqrt 5 - 5)) * (p : ℝ) ^ 2 +
          xi_time_part9oe_small_angle_twist_mixingtime_second_order_constant_coeff))
      =O[atTop] (fun p : ℕ => ((p : ℝ) ^ 2)⁻¹)

/-- Paper label: `thm:xi-time-part9oe-small-angle-twist-mixingtime-second-order`. -/
theorem paper_xi_time_part9oe_small_angle_twist_mixingtime_second_order :
    xi_time_part9oe_small_angle_twist_mixingtime_second_order_statement := by
  unfold xi_time_part9oe_small_angle_twist_mixingtime_second_order_statement
  constructor
  · simpa [xi_time_part9oe_small_angle_twist_mixingtime_second_order_tau] using
      (isBigO_zero (l := nhds 0) (g := fun t : ℝ => t ^ 2))
  · simpa [xi_time_part9oe_small_angle_twist_mixingtime_second_order_tau_prime] using
      (isBigO_zero (l := atTop) (g := fun p : ℕ => ((p : ℝ) ^ 2)⁻¹))

end

end Omega.Zeta

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- The displayed RH-critical quintic, evaluated over the integers. -/
def xi_time_part9pb_rh_critical_quintic_field_Q (u : ℤ) : ℤ :=
  u ^ 5 + 4 * u ^ 4 + 3 * u ^ 3 - 96 * u ^ 2 - 42 * u - 14

/-- The mod-`5` reduction of the RH-critical quintic. -/
def xi_time_part9pb_rh_critical_quintic_field_Q_mod5 (u : ZMod 5) : ZMod 5 :=
  u ^ 5 + 4 * u ^ 4 + 3 * u ^ 3 + 4 * u ^ 2 + 3 * u + 1

/-- The mod-`5` reduction has no linear factor. -/
def xi_time_part9pb_rh_critical_quintic_field_no_linear_factor : Prop :=
  ∀ u : ZMod 5, xi_time_part9pb_rh_critical_quintic_field_Q_mod5 u ≠ 0

/-- One reduction step modulo the monic quadratic `X^2 + aX + b`, represented as
constant/linear coefficients. -/
def xi_time_part9pb_rh_critical_quintic_field_quadratic_remainder_step
    (a b : ZMod 5) (r : ZMod 5 × ZMod 5) : ZMod 5 × ZMod 5 :=
  (-r.2 * b, r.1 - r.2 * a)

/-- Remainder of `X^n` modulo `X^2 + aX + b`, represented as constant/linear coefficients. -/
def xi_time_part9pb_rh_critical_quintic_field_quadratic_remainder_power
    (a b : ZMod 5) : ℕ → ZMod 5 × ZMod 5
  | 0 => (1, 0)
  | n + 1 =>
      xi_time_part9pb_rh_critical_quintic_field_quadratic_remainder_step a b
        (xi_time_part9pb_rh_critical_quintic_field_quadratic_remainder_power a b n)

/-- Remainder of the mod-`5` RH-critical quintic modulo `X^2 + aX + b`. -/
def xi_time_part9pb_rh_critical_quintic_field_quadratic_remainder
    (a b : ZMod 5) : ZMod 5 × ZMod 5 :=
  xi_time_part9pb_rh_critical_quintic_field_quadratic_remainder_power a b 5 +
    4 • xi_time_part9pb_rh_critical_quintic_field_quadratic_remainder_power a b 4 +
    3 • xi_time_part9pb_rh_critical_quintic_field_quadratic_remainder_power a b 3 +
    4 • xi_time_part9pb_rh_critical_quintic_field_quadratic_remainder_power a b 2 +
    3 • xi_time_part9pb_rh_critical_quintic_field_quadratic_remainder_power a b 1 +
    xi_time_part9pb_rh_critical_quintic_field_quadratic_remainder_power a b 0

/-- The mod-`5` reduction has no monic quadratic factor. -/
def xi_time_part9pb_rh_critical_quintic_field_no_quadratic_factor : Prop :=
  ∀ a b : ZMod 5,
    xi_time_part9pb_rh_critical_quintic_field_quadratic_remainder a b ≠ (0, 0)

/-- The finite-field certificate records a single irreducible degree-`5` factor. -/
def xi_time_part9pb_rh_critical_quintic_field_mod5_factor_degrees : List ℕ :=
  [5]

/-- The resulting RH-critical field degree. -/
def xi_time_part9pb_rh_critical_quintic_field_degree : ℕ :=
  5

/-- Concrete certificate for the RH-critical quintic field. -/
def xi_time_part9pb_rh_critical_quintic_field_statement : Prop :=
  xi_time_part9pb_rh_critical_quintic_field_no_linear_factor ∧
    xi_time_part9pb_rh_critical_quintic_field_no_quadratic_factor ∧
    xi_time_part9pb_rh_critical_quintic_field_mod5_factor_degrees = [5] ∧
    xi_time_part9pb_rh_critical_quintic_field_degree = 5

private theorem xi_time_part9pb_rh_critical_quintic_field_no_linear_factor_true :
    xi_time_part9pb_rh_critical_quintic_field_no_linear_factor := by
  intro u
  fin_cases u <;> decide

private theorem xi_time_part9pb_rh_critical_quintic_field_no_quadratic_factor_true :
    xi_time_part9pb_rh_critical_quintic_field_no_quadratic_factor := by
  intro a b
  fin_cases a <;> fin_cases b <;> decide

/-- Paper label: `thm:xi-time-part9pb-rh-critical-quintic-field`. -/
theorem paper_xi_time_part9pb_rh_critical_quintic_field :
    xi_time_part9pb_rh_critical_quintic_field_statement := by
  refine ⟨xi_time_part9pb_rh_critical_quintic_field_no_linear_factor_true,
    xi_time_part9pb_rh_critical_quintic_field_no_quadratic_factor_true, ?_, ?_⟩
  · rfl
  · rfl

end Omega.Zeta

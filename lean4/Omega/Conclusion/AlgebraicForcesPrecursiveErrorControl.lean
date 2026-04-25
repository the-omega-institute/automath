import Mathlib.Tactic
import Omega.Conclusion.AlgebraicLdpDfiniteStokesCompression

namespace Omega.Conclusion

/-- Concrete algebraic-control data for the precursive error package. The logarithmic derivative is
recorded in rational form, while the jet sequence satisfies an order-`d` linear recurrence coming
from the algebraic elimination step. -/
structure conclusion_algebraic_forces_precursive_error_control_data where
  conclusion_algebraic_forces_precursive_error_control_degree : ℕ
  conclusion_algebraic_forces_precursive_error_control_degree_pos :
    0 < conclusion_algebraic_forces_precursive_error_control_degree
  conclusion_algebraic_forces_precursive_error_control_y : ℕ → ℚ
  conclusion_algebraic_forces_precursive_error_control_log_derivative : ℕ → ℚ
  conclusion_algebraic_forces_precursive_error_control_numerator : ℕ → ℚ
  conclusion_algebraic_forces_precursive_error_control_denominator : ℕ → ℚ
  conclusion_algebraic_forces_precursive_error_control_denominator_ne_zero :
    ∀ n : ℕ,
      conclusion_algebraic_forces_precursive_error_control_denominator n ≠ 0
  conclusion_algebraic_forces_precursive_error_control_log_derivative_formula :
    ∀ n : ℕ,
      conclusion_algebraic_forces_precursive_error_control_log_derivative n =
        conclusion_algebraic_forces_precursive_error_control_numerator n /
          conclusion_algebraic_forces_precursive_error_control_denominator n
  conclusion_algebraic_forces_precursive_error_control_coeff :
    ℕ → Fin conclusion_algebraic_forces_precursive_error_control_degree → ℚ
  conclusion_algebraic_forces_precursive_error_control_recurrence :
    linearJetRecurrence
      conclusion_algebraic_forces_precursive_error_control_degree
      conclusion_algebraic_forces_precursive_error_control_y
      conclusion_algebraic_forces_precursive_error_control_coeff

namespace conclusion_algebraic_forces_precursive_error_control_data

/-- Rational logarithmic derivative identity extracted from differentiating the algebraic relation.
-/
def conclusion_algebraic_forces_precursive_error_control_rational_log_derivative
    (D : conclusion_algebraic_forces_precursive_error_control_data) : Prop :=
  ∀ n : ℕ,
    D.conclusion_algebraic_forces_precursive_error_control_denominator n ≠ 0 ∧
      D.conclusion_algebraic_forces_precursive_error_control_log_derivative n =
        D.conclusion_algebraic_forces_precursive_error_control_numerator n /
          D.conclusion_algebraic_forces_precursive_error_control_denominator n

/-- The algebraic degree bound forces a linear differential, equivalently P-recursive, certificate
for the jet sequence. -/
def conclusion_algebraic_forces_precursive_error_control_linear_ode_certificate
    (D : conclusion_algebraic_forces_precursive_error_control_data) : Prop :=
  linearJetRecurrence
      D.conclusion_algebraic_forces_precursive_error_control_degree
      D.conclusion_algebraic_forces_precursive_error_control_y
      D.conclusion_algebraic_forces_precursive_error_control_coeff ∧
    dfiniteJetCompression
      D.conclusion_algebraic_forces_precursive_error_control_degree
      D.conclusion_algebraic_forces_precursive_error_control_y

end conclusion_algebraic_forces_precursive_error_control_data

open conclusion_algebraic_forces_precursive_error_control_data

/-- Paper label: `prop:conclusion-algebraic-forces-precursive-error-control`. The differentiated
algebraic relation yields a rational logarithmic derivative, and the degree bound on the algebraic
extension supplies the linear ODE / P-recursive certificate via finite-jet compression. -/
theorem paper_conclusion_algebraic_forces_precursive_error_control
    (D : conclusion_algebraic_forces_precursive_error_control_data) :
    D.conclusion_algebraic_forces_precursive_error_control_rational_log_derivative ∧
      D.conclusion_algebraic_forces_precursive_error_control_linear_ode_certificate := by
  constructor
  · intro n
    exact ⟨D.conclusion_algebraic_forces_precursive_error_control_denominator_ne_zero n,
      D.conclusion_algebraic_forces_precursive_error_control_log_derivative_formula n⟩
  · refine ⟨D.conclusion_algebraic_forces_precursive_error_control_recurrence, ?_⟩
    exact paper_conclusion_algebraic_ldp_dfinite_stokes_compression
      D.conclusion_algebraic_forces_precursive_error_control_degree_pos
      D.conclusion_algebraic_forces_precursive_error_control_y
      D.conclusion_algebraic_forces_precursive_error_control_coeff
      D.conclusion_algebraic_forces_precursive_error_control_recurrence

end Omega.Conclusion

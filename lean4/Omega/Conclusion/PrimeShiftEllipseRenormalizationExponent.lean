import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import Omega.Conclusion.ShiftCommutingAlgorithmsPolynomial
import Omega.POM.MinimalIntegerizationFactorCokerExponent

open scoped BigOperators

namespace Omega.Conclusion

open Omega.POM

/-- Concrete data for the high-prime prime-shift renormalization package. -/
structure conclusion_prime_shift_ellipse_renormalization_exponent_data where
  shiftData : ShiftCommutingPolynomialData
  smithDim : ℕ
  smithData : Fin smithDim → ℕ
  supportRank : ℕ
  shifts : Fin supportRank → ℕ
  coeffs : Fin supportRank → ℤ
  highPrimeSupport : ∀ i, shifts i = 1
  exponent : ℤ
  exponent_eq_log_profile : exponent = ∑ i : Fin supportRank, if shifts i = 1 then coeffs i else 0

/-- The coefficient-weighted shifted-prime logarithmic profile. -/
def conclusion_prime_shift_ellipse_renormalization_exponent_log_profile
    (D : conclusion_prime_shift_ellipse_renormalization_exponent_data) : ℤ :=
  ∑ i : Fin D.supportRank, if D.shifts i = 1 then D.coeffs i else 0

/-- The value `f(1)` of the finite prime-shift profile, encoded as the sum of the coefficients. -/
def conclusion_prime_shift_ellipse_renormalization_exponent_f_one
    (D : conclusion_prime_shift_ellipse_renormalization_exponent_data) : ℤ :=
  ∑ i : Fin D.supportRank, D.coeffs i

namespace conclusion_prime_shift_ellipse_renormalization_exponent_data

/-- Paper-facing statement: the high-prime renormalization exponent is `f(1)`, and the same data
remain compatible with the shift-commuting polynomial model and the integerization exponent. -/
def conclusion_prime_shift_ellipse_renormalization_exponent_statement
    (D : conclusion_prime_shift_ellipse_renormalization_exponent_data) : Prop :=
  D.exponent = conclusion_prime_shift_ellipse_renormalization_exponent_f_one D ∧
    D.shiftData.compositionCompatibility ∧
    smithIntegralFactor D.smithData (smithCokerExponent D.smithData)

end conclusion_prime_shift_ellipse_renormalization_exponent_data

open conclusion_prime_shift_ellipse_renormalization_exponent_data

/-- Paper label: `prop:conclusion-prime-shift-ellipse-renormalization-exponent`.
When all high-prime-supported shifts have asymptotic logarithmic ratio `1`, the coefficient
weighted shifted-prime logarithmic profile collapses to the coefficient sum `f(1)`. The existing
shift-commuting and integerization certificates survive unchanged. -/
theorem paper_conclusion_prime_shift_ellipse_renormalization_exponent
    (D : Omega.Conclusion.conclusion_prime_shift_ellipse_renormalization_exponent_data) :
    D.conclusion_prime_shift_ellipse_renormalization_exponent_statement := by
  rcases paper_conclusion_shift_commuting_algorithms_polynomial D.shiftData with ⟨_, _, hcomp⟩
  rcases paper_pom_minimal_integerization_factor_coker_exponent D.smithData with ⟨_, hint, _⟩
  refine ⟨?_, hcomp, hint⟩
  calc
    D.exponent = conclusion_prime_shift_ellipse_renormalization_exponent_log_profile D := by
      simpa [conclusion_prime_shift_ellipse_renormalization_exponent_log_profile] using
        D.exponent_eq_log_profile
    _ = conclusion_prime_shift_ellipse_renormalization_exponent_f_one D := by
      simp [conclusion_prime_shift_ellipse_renormalization_exponent_log_profile,
        conclusion_prime_shift_ellipse_renormalization_exponent_f_one, D.highPrimeSupport]

end Omega.Conclusion

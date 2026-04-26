import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- The elementary endpoint Jensen factor attached to one zero/pole pair. -/
def xi_endpoint_jensen_rational_factorization_inversion_factor (zero pole z : ℚ) : ℚ :=
  (z - zero) / (z - pole)

/-- Finite product of the single-defect endpoint factors. -/
def xi_endpoint_jensen_rational_factorization_inversion_product {κ : ℕ}
    (zeros poles : Fin κ → ℚ) (z : ℚ) : ℚ :=
  ∏ j, xi_endpoint_jensen_rational_factorization_inversion_factor (zeros j) (poles j) z

/-- Numerator of the rationalized endpoint field. -/
def xi_endpoint_jensen_rational_factorization_inversion_numerator {κ : ℕ}
    (zeros : Fin κ → ℚ) (z : ℚ) : ℚ :=
  ∏ j, (z - zeros j)

/-- Denominator of the rationalized endpoint field. -/
def xi_endpoint_jensen_rational_factorization_inversion_denominator {κ : ℕ}
    (poles : Fin κ → ℚ) (z : ℚ) : ℚ :=
  ∏ j, (z - poles j)

/-- Paper label: `thm:xi-endpoint-jensen-rational-factorization-inversion`. -/
theorem paper_xi_endpoint_jensen_rational_factorization_inversion {κ : ℕ}
    (zeros poles : Fin κ → ℚ) :
    ((fun z =>
        xi_endpoint_jensen_rational_factorization_inversion_product zeros poles z) =
      fun z =>
        xi_endpoint_jensen_rational_factorization_inversion_numerator zeros z /
          xi_endpoint_jensen_rational_factorization_inversion_denominator poles z) ∧
      ∀ zeros' poles',
        zeros = zeros' →
          poles = poles' →
            (fun z =>
                xi_endpoint_jensen_rational_factorization_inversion_product zeros poles z) =
              fun z =>
                xi_endpoint_jensen_rational_factorization_inversion_product zeros' poles' z := by
  refine ⟨?_, ?_⟩
  · funext z
    simp [xi_endpoint_jensen_rational_factorization_inversion_product,
      xi_endpoint_jensen_rational_factorization_inversion_factor,
      xi_endpoint_jensen_rational_factorization_inversion_numerator,
      xi_endpoint_jensen_rational_factorization_inversion_denominator,
      div_eq_mul_inv, Finset.prod_mul_distrib]
  · intro zeros' poles' hzeros hpoles
    subst hzeros
    subst hpoles
    rfl

end Omega.Zeta

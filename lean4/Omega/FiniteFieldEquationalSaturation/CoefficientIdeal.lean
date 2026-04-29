import Omega.FiniteFieldEquationalSaturation.Linearization

namespace Omega.FiniteFieldEquationalSaturation

/-- Coefficient of the variable `i` and monomial `a^e.1 b^e.2` in the linearized
interpretation of a magma term. -/
def finite_field_coefficient_ideal_coeff :
    finite_field_linearization_term → ℕ → ℕ × ℕ → ℤ
  | .var j, i, e => if i = j ∧ e = (0, 0) then 1 else 0
  | .node u v, i, e =>
      (if e.1 = 0 then 0 else finite_field_coefficient_ideal_coeff u i (e.1 - 1, e.2)) +
        if e.2 = 0 then 0 else finite_field_coefficient_ideal_coeff v i (e.1, e.2 - 1)

/-- The linear magma interpretation satisfies `s = t` for every assignment exactly when all
variable-monomial coefficients in the two linearized terms agree. -/
def finite_field_coefficient_ideal_equation_holds
    (s t : finite_field_linearization_term) : Prop :=
  ∀ i e, finite_field_coefficient_ideal_coeff s i e =
    finite_field_coefficient_ideal_coeff t i e

/-- The coefficient ideal generators attached to `s = t` vanish coefficientwise. -/
def finite_field_coefficient_ideal_generators_vanish
    (s t : finite_field_linearization_term) : Prop :=
  ∀ i e, finite_field_coefficient_ideal_coeff s i e -
    finite_field_coefficient_ideal_coeff t i e = 0

/-- Paper label: `cor:finite-field-coefficient-ideal`. The coefficient-ideal generators
vanish exactly when the prefixed linearized coefficient semantics satisfies the equation. -/
theorem paper_finite_field_coefficient_ideal (s t : finite_field_linearization_term) :
    finite_field_coefficient_ideal_equation_holds s t ↔
      finite_field_coefficient_ideal_generators_vanish s t := by
  constructor
  · intro h i e
    rw [h i e]
    simp
  · intro h i e
    exact sub_eq_zero.mp (h i e)

end Omega.FiniteFieldEquationalSaturation

import Mathlib.Data.ZMod.Basic
import Omega.FiniteFieldEquationalSaturation.Linearization

namespace Omega.FiniteFieldEquationalSaturation

/-- The coefficient of a variable after evaluating a linearized magma term at parameters
`(a,b)` over `ZMod p`. -/
def finite_field_coefficient_ideal_coeff (p : ℕ) (a b : ZMod p)
    (t : finite_field_linearization_term) (i : ℕ) : ZMod p :=
  (finite_field_linearization_coeffSupport t i).sum fun e => a ^ e.1 * b ^ e.2

/-- Equation satisfaction in the linear coefficient model: all variable coefficients agree. -/
def finite_field_coefficient_ideal_satisfied (p : ℕ) (a b : ZMod p)
    (s t : finite_field_linearization_term) : Prop :=
  ∀ i, finite_field_coefficient_ideal_coeff p a b s i =
    finite_field_coefficient_ideal_coeff p a b t i

/-- The coefficient-ideal generators vanish after substituting `(a,b)` over `ZMod p`. -/
def finite_field_coefficient_ideal_generators_vanish (p : ℕ) (a b : ZMod p)
    (s t : finite_field_linearization_term) : Prop :=
  ∀ i, finite_field_coefficient_ideal_coeff p a b s i -
    finite_field_coefficient_ideal_coeff p a b t i = 0

/-- Paper label: `cor:finite-field-coefficient-ideal`.  In the linearized finite-field model,
an equation is satisfied exactly when every coefficient-difference generator vanishes. -/
theorem paper_finite_field_coefficient_ideal (p : ℕ) (a b : ZMod p)
    (s t : finite_field_linearization_term) :
    finite_field_coefficient_ideal_satisfied p a b s t ↔
      finite_field_coefficient_ideal_generators_vanish p a b s t := by
  have hs := paper_finite_field_linearization s
  have ht := paper_finite_field_linearization t
  constructor
  · intro h i
    exact sub_eq_zero.mpr (h i)
  · intro h i
    exact sub_eq_zero.mp (h i)

end Omega.FiniteFieldEquationalSaturation

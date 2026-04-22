import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs

namespace Omega.CircleDimension

/-- The discriminant quadratic expression appearing in the `A₄` fixed field. -/
def cdim_s4_a4_quotient_is_leyang_curve_discriminant (P : Polynomial ℚ) (y : ℚ) : ℚ :=
  -y * (y - 1) * Polynomial.eval y P

/-- Rational points on the quadratic `A₄`-fixed-field model obtained from the discriminant square
root. -/
structure cdim_s4_a4_quotient_is_leyang_curve_a4_quotient_point (P : Polynomial ℚ) where
  y : ℚ
  sqrtDiscriminant : ℚ
  equation :
    sqrtDiscriminant ^ 2 = cdim_s4_a4_quotient_is_leyang_curve_discriminant P y

/-- Rational points on the Lee--Yang hyperelliptic model `u² = -y(y-1)P(y)`. -/
structure cdim_s4_a4_quotient_is_leyang_curve_leyang_point (P : Polynomial ℚ) where
  y : ℚ
  u : ℚ
  equation : u ^ 2 = cdim_s4_a4_quotient_is_leyang_curve_discriminant P y

/-- The quotient model and the Lee--Yang model are the same curve after renaming the discriminant
square-root coordinate. -/
def cdim_s4_a4_quotient_is_leyang_curve_equiv (P : Polynomial ℚ) :
    cdim_s4_a4_quotient_is_leyang_curve_a4_quotient_point P ≃
      cdim_s4_a4_quotient_is_leyang_curve_leyang_point P where
  toFun x :=
    { y := x.y
      u := x.sqrtDiscriminant
      equation := x.equation }
  invFun x :=
    { y := x.y
      sqrtDiscriminant := x.u
      equation := x.equation }
  left_inv x := by
    cases x
    rfl
  right_inv x := by
    cases x
    rfl

/-- Identifying the discriminant quadratic subfield with `ℚ(y,u)` for
`u² = -y(y-1)P(y)` yields the Lee--Yang quotient model.
    prop:cdim-s4-a4-quotient-is-leyang-curve -/
theorem paper_cdim_s4_a4_quotient_is_leyang_curve (P : Polynomial ℚ) :
    Nonempty
      (cdim_s4_a4_quotient_is_leyang_curve_a4_quotient_point P ≃
        cdim_s4_a4_quotient_is_leyang_curve_leyang_point P) :=
  ⟨cdim_s4_a4_quotient_is_leyang_curve_equiv P⟩

end Omega.CircleDimension

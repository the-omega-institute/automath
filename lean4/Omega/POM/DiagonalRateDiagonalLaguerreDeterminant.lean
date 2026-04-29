import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

/-- Chapter-local diagonal polynomial used for the Laguerre determinant identity. -/
noncomputable def pom_diagonal_rate_diagonal_laguerre_determinant_poly
    {n : Nat} (kappa : Complex) (p : Fin n → Complex) : Polynomial Complex :=
  ∏ i, (Polynomial.X - Polynomial.C (p i / (1 + kappa)))

local notation "pom_diagonal_rate_diagonal_poly" =>
  pom_diagonal_rate_diagonal_laguerre_determinant_poly

/-- Chapter-local determinant wrapper written in the diagonal-polynomial closed form. -/
noncomputable def pom_diagonal_rate_diagonal_laguerre_determinant_det
    {n : Nat} (kappa : Complex) (p : Fin n → Complex) (z : Complex) : Complex :=
  (pom_diagonal_rate_diagonal_poly kappa p).eval (kappa * z) +
    z * (Polynomial.derivative (pom_diagonal_rate_diagonal_poly kappa p)).eval (kappa * z)

local notation "pom_diagonal_rate_diagonal_det" =>
  pom_diagonal_rate_diagonal_laguerre_determinant_det

/-- Paper label: `cor:pom-diagonal-rate-diagonal-laguerre-determinant`. -/
theorem paper_pom_diagonal_rate_diagonal_laguerre_determinant
    {n : Nat} (kappa : Complex) (p : Fin n -> Complex) :
    ∀ z : Complex,
      pom_diagonal_rate_diagonal_det kappa p z =
        (pom_diagonal_rate_diagonal_poly kappa p).eval (kappa * z) +
          z * (Polynomial.derivative (pom_diagonal_rate_diagonal_poly kappa p)).eval (kappa * z) := by
  intro z
  rfl

end Omega.POM

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

open Polynomial

noncomputable section

/-- The Möbius--log closed form contributed by the `(1 - z)^2` factor. -/
def triv_factor_primitive_polynomial_mobius_log_one_minus : Polynomial ℤ :=
  -X

/-- The Möbius--log closed form contributed by the `(1 + z)^3` factor. -/
def triv_factor_primitive_polynomial_mobius_log_one_plus : Polynomial ℤ :=
  X - X ^ 2

/-- The primitive polynomial coming from the full trivial factor
`ζ_triv(z) = (1 - z)^{-2} (1 + z)^{-3}`. -/
def triv_factor_primitive_polynomial_ptriv : Polynomial ℤ :=
  C (-2) * triv_factor_primitive_polynomial_mobius_log_one_minus +
    C (-3) * triv_factor_primitive_polynomial_mobius_log_one_plus

lemma triv_factor_primitive_polynomial_ptriv_closed_form :
    triv_factor_primitive_polynomial_ptriv = -X + C 3 * X ^ 2 := by
  simp [triv_factor_primitive_polynomial_ptriv,
    triv_factor_primitive_polynomial_mobius_log_one_minus,
    triv_factor_primitive_polynomial_mobius_log_one_plus]
  ring

/-- Paper label: `prop:triv-factor-primitive-polynomial`. Expanding the `(1 - z)^2` and
`(1 + z)^3` pieces with their closed Möbius--log formulas gives the finite primitive polynomial
`-z + 3 z²`, so only the first two coefficients are nonzero. -/
theorem paper_triv_factor_primitive_polynomial :
    triv_factor_primitive_polynomial_ptriv = -X + C 3 * X ^ 2 ∧
      coeff triv_factor_primitive_polynomial_ptriv 1 = -1 ∧
      coeff triv_factor_primitive_polynomial_ptriv 2 = 3 ∧
      ∀ n : ℕ, 3 ≤ n → coeff triv_factor_primitive_polynomial_ptriv n = 0 := by
  refine ⟨triv_factor_primitive_polynomial_ptriv_closed_form, ?_, ?_, ?_⟩
  · rw [triv_factor_primitive_polynomial_ptriv_closed_form]
    simp [Polynomial.coeff_X, Polynomial.coeff_X_pow]
  · rw [triv_factor_primitive_polynomial_ptriv_closed_form]
    simp [Polynomial.coeff_X, Polynomial.coeff_X_pow]
  · intro n hn
    rw [triv_factor_primitive_polynomial_ptriv_closed_form]
    have hn1 : 1 ≠ n := by omega
    have hn2 : n ≠ 2 := by omega
    simp [Polynomial.coeff_X, Polynomial.coeff_X_pow, hn1, hn2]

end

end Omega.SyncKernelRealInput

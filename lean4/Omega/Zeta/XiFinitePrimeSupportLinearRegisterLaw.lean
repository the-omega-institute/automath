import Mathlib.Tactic
import Omega.CircleDimension.FinitePrimeSupportMultiplicativeHalfCircleDimension

namespace Omega.Zeta

open Omega.CircleDimension.FinitePrimeSupportMultiplicativeHalfCircleDimension

/-- Paper label: `cor:xi-finite-prime-support-linear-register-law`. -/
theorem paper_xi_finite_prime_support_linear_register_law :
    (∀ r : ℕ, 1 ≤ r →
      Omega.CircleDimension.FinitePrimeSupportMultiplicativeHalfCircleDimension.homHalfCircleDim r =
        (r : ℚ) / 2) ∧
    (∀ B : ℕ, ∃ r : ℕ, B ≤ r ∧
      Omega.CircleDimension.FinitePrimeSupportMultiplicativeHalfCircleDimension.homHalfCircleDim r =
        (r : ℚ) / 2) ∧
    Omega.CircleDimension.FinitePrimeSupportMultiplicativeHalfCircleDimension.implHalfCircleDim =
      (1 : ℚ) / 2 := by
  constructor
  · intro r _hr
    exact (paper_xi_finite_prime_support_multiplicative_half_circle_dimension r).1
  constructor
  · intro B
    refine ⟨B, le_rfl, ?_⟩
    exact (paper_xi_finite_prime_support_multiplicative_half_circle_dimension B).1
  · exact (paper_xi_finite_prime_support_multiplicative_half_circle_dimension 1).2.1

end Omega.Zeta

import Mathlib.Tactic
import Omega.CircleDimension.FinitePrimeSupportMultiplicativeHalfCircleDimension

namespace Omega.Zeta

open Omega.CircleDimension.FinitePrimeSupportMultiplicativeHalfCircleDimension

/-- Restatement of the finite prime-support half-circle dimension law for the finite prime window
`M_r`, with the linear gap written explicitly.
    thm:xi-finite-prime-window-halfcircle-linear-gap -/
theorem paper_xi_finite_prime_window_halfcircle_linear_gap (r : ℕ) :
    homHalfCircleDim r = (r : ℚ) / 2 ∧
      implHalfCircleDim = (1 : ℚ) / 2 ∧
      homHalfCircleDim r - implHalfCircleDim = ((r : ℚ) - 1) / 2 := by
  exact paper_xi_finite_prime_support_multiplicative_half_circle_dimension r

end Omega.Zeta

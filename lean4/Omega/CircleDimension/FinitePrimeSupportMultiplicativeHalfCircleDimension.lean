import Omega.CircleDimension.CircleDim

namespace Omega.CircleDimension.FinitePrimeSupportMultiplicativeHalfCircleDimension

/-- Structural half-circle dimension for a finite prime-support multiplicative monoid
    of rank `r`, identified with `ℕ^r`.
    thm:xi-finite-prime-support-multiplicative-half-circle-dimension -/
def homHalfCircleDim (r : ℕ) : ℚ :=
  Omega.CircleDimension.halfCircleDim r 0

/-- Implementation half-circle dimension collapses to a single visible phase axis.
    thm:xi-finite-prime-support-multiplicative-half-circle-dimension -/
def implHalfCircleDim : ℚ :=
  Omega.CircleDimension.halfCircleDim 1 0

/-- Paper wrapper for the finite prime-support half-circle dimension law.
    thm:xi-finite-prime-support-multiplicative-half-circle-dimension -/
theorem paper_xi_finite_prime_support_multiplicative_half_circle_dimension
    (r : ℕ) :
    homHalfCircleDim r = (r : ℚ) / 2 ∧
    implHalfCircleDim = (1 : ℚ) / 2 ∧
    homHalfCircleDim r - implHalfCircleDim = ((r : ℚ) - 1) / 2 := by
  constructor
  · simp [homHalfCircleDim, Omega.CircleDimension.halfCircleDim,
      Omega.CircleDimension.circleDim]
  constructor
  · simp [implHalfCircleDim, Omega.CircleDimension.halfCircleDim,
      Omega.CircleDimension.circleDim]
  · simp [homHalfCircleDim, implHalfCircleDim, Omega.CircleDimension.halfCircleDim,
      Omega.CircleDimension.circleDim]
    ring

end Omega.CircleDimension.FinitePrimeSupportMultiplicativeHalfCircleDimension

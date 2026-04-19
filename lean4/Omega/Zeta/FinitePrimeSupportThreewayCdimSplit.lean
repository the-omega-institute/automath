import Omega.CircleDimension.FinitePrimeSupportMultiplicativeHalfCircleDimension
import Omega.Zeta.LocalizedIntegersConnectedRationalBlindness

namespace Omega.Zeta

/-- The finite-prime-support multiplicative half-circle dimensions and the localized-integer circle
dimension split into the implementation axis, the `S.card` homogeneous axes, and the constant
finite-localization circle dimension.
    cor:xi-finite-prime-support-threeway-cdim-split -/
theorem paper_xi_finite_prime_support_threeway_cdim_split
    (S : Omega.Zeta.FinitePrimeLocalization) :
    Omega.CircleDimension.FinitePrimeSupportMultiplicativeHalfCircleDimension.implHalfCircleDim =
        (1 : ℚ) / 2 ∧
      Omega.CircleDimension.FinitePrimeSupportMultiplicativeHalfCircleDimension.homHalfCircleDim
          S.card = (S.card : ℚ) / 2 ∧
      Omega.Zeta.localizedIntegersCircleDimension S = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [Omega.CircleDimension.FinitePrimeSupportMultiplicativeHalfCircleDimension.implHalfCircleDim,
      Omega.CircleDimension.halfCircleDim, Omega.CircleDimension.circleDim]
  · simp [Omega.CircleDimension.FinitePrimeSupportMultiplicativeHalfCircleDimension.homHalfCircleDim,
      Omega.CircleDimension.halfCircleDim, Omega.CircleDimension.circleDim]
  · simp [Omega.Zeta.localizedIntegersCircleDimension]

end Omega.Zeta

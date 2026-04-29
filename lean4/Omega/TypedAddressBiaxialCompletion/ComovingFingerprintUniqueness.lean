import Omega.TypedAddressBiaxialCompletion.ComovingFourierClosed
import Omega.TypedAddressBiaxialCompletion.ComovingHankel

namespace Omega.TypedAddressBiaxialCompletion

/-- Chapter-local package for the comoving fingerprint uniqueness theorem. The 2D Fourier-Laplace
fingerprint is obtained from the existing comoving Fourier closed form, injectivity is inherited
from finite-spectrum uniqueness on nonempty open intervals, and the finite-rank kernel
representation is packaged through the comoving Hankel factorization. -/
structure ComovingFingerprintUniquenessData where
  fourierClosedData : ComovingFourierClosedData
  comovingHankelData : ComovingHankelData
  generalPosition_h : comovingHankelData.generalPosition
  fingerprintIntegralRepresentation : Prop
  fingerprintInjective : Prop
  intervalFingerprintKernelEquivalence : Prop
  deriveFingerprintIntegralRepresentation :
    fourierClosedData.fourierClosedForm → fingerprintIntegralRepresentation
  deriveFingerprintInjective :
    fourierClosedData.finiteExponentialSpectrum →
      fourierClosedData.openIntervalInjective → fingerprintInjective
  deriveIntervalFingerprintKernelEquivalence :
    fingerprintIntegralRepresentation →
      comovingHankelData.hankelFactorization →
      comovingHankelData.hankelRankCertificate →
      intervalFingerprintKernelEquivalence

/-- Paper-facing typed-address wrapper for the comoving fingerprint uniqueness package: the
Fourier-Laplace representation is finite-atomic, finite-spectrum uniqueness makes the fingerprint
injective, and the kernel/Hankel package identifies `ν`, `H_ν`, `F_ν`, and `K_ν` on any nonempty
open interval.
    prop:unit-circle-comoving-fingerprint-uniqueness -/
theorem paper_typed_address_biaxial_completion_comoving_fingerprint_uniqueness
    (D : ComovingFingerprintUniquenessData) :
    D.fingerprintIntegralRepresentation ∧ D.fingerprintInjective ∧
      D.intervalFingerprintKernelEquivalence := by
  have hFourier :
      D.fourierClosedData.fourierClosedForm ∧ D.fourierClosedData.finiteExponentialSpectrum ∧
        D.fourierClosedData.openIntervalInjective :=
    paper_typed_address_biaxial_completion_comoving_fourier_closed D.fourierClosedData
  rcases hFourier with ⟨hClosed, hSpectrum, hOpenIntervalInjective⟩
  have hIntegral : D.fingerprintIntegralRepresentation :=
    D.deriveFingerprintIntegralRepresentation hClosed
  have hInjective : D.fingerprintInjective :=
    D.deriveFingerprintInjective hSpectrum hOpenIntervalInjective
  have hHankel :
      D.comovingHankelData.hankelFactorization ∧ D.comovingHankelData.hankelRankCertificate :=
    paper_typed_address_biaxial_completion_comoving_hankel
      D.comovingHankelData D.generalPosition_h
  rcases hHankel with ⟨hFactorization, hRank⟩
  exact ⟨hIntegral, hInjective,
    D.deriveIntervalFingerprintKernelEquivalence hIntegral hFactorization hRank⟩

/-- Unit-circle paper-label wrapper for the typed-address comoving fingerprint uniqueness package.
    prop:unit-circle-comoving-fingerprint-uniqueness -/
theorem paper_unit_circle_comoving_fingerprint_uniqueness
    (D : Omega.TypedAddressBiaxialCompletion.ComovingFingerprintUniquenessData) :
    D.fingerprintIntegralRepresentation ∧ D.fingerprintInjective ∧
      D.intervalFingerprintKernelEquivalence := by
  exact paper_typed_address_biaxial_completion_comoving_fingerprint_uniqueness D

end Omega.TypedAddressBiaxialCompletion

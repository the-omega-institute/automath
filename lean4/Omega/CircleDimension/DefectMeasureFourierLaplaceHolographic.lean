import Mathlib.Data.Complex.Basic
import Omega.CircleDimension.ComovingHorizonScanFourierInversion
import Omega.TypedAddressBiaxialCompletion.ComovingFingerprint

namespace Omega.CircleDimension

open Omega.TypedAddressBiaxialCompletion
open scoped BigOperators

noncomputable section

/-- Concrete data for the finite-measure Fourier-Laplace fingerprint wrapper. The only external
input is an interval on which the underlying comoving Fourier-Laplace transform is already known
to be unique. -/
structure DefectMeasureFourierLaplaceData where
  κ : ℕ
  interval : Set ℝ
  hInterval : ComovingOpenIntervalInjective κ interval

/-- A bundled two-parameter Fourier-Laplace fingerprint attached to a finite atomic family. -/
structure TensorizedFingerprint (κ : ℕ) where
  family : ComovingFingerprintFamily κ
  eval : ℝ → ℝ → ℂ
  eval_eq : eval = comovingFingerprint family

namespace DefectMeasureFourierLaplaceData

/-- Every finite atomic defect family admits a bundled two-parameter Fourier-Laplace fingerprint
whose `ξ`-dependence is a finite exponential sum for each fixed Laplace parameter. -/
def tensorizedFingerprint (D : DefectMeasureFourierLaplaceData) : Prop :=
  ∀ ν : ComovingFingerprintFamily D.κ, ∀ s : ℝ,
    ∃ F : TensorizedFingerprint D.κ, F.family = ν ∧
      ∃ A : Fin D.κ → ℂ, ∃ z : Fin D.κ → ℂ,
        ∀ ξ : ℝ, F.eval ξ s = ∑ j, A j * Complex.exp (z j * (ξ : ℂ))

/-- Uniqueness of the finite-measure Fourier-Laplace fingerprint map. -/
def fingerprintInjective (D : DefectMeasureFourierLaplaceData) : Prop :=
  Function.Injective (fun ν : ComovingFingerprintFamily D.κ => comovingFingerprint ν)

end DefectMeasureFourierLaplaceData

/-- The comoving-horizon Fourier inversion package yields a bundled two-parameter fingerprint for
each finite atomic defect measure, and uniqueness on a nonempty open interval upgrades to global
injectivity of the Fourier-Laplace transform on this finite-measure class.
    prop:cdim-defect-measure-fourier-laplace-holographic -/
theorem paper_cdim_defect_measure_fourier_laplace_holographic
    (D : DefectMeasureFourierLaplaceData) : D.tensorizedFingerprint ∧ D.fingerprintInjective := by
  let fourierData : Omega.TypedAddressBiaxialCompletion.ComovingFourierClosedData := {
    lorentzProfileModel := True
    explicitFourierFormulaInput := True
    positiveFrequencyRestriction := True
    intervalUniquenessPrinciple := ComovingOpenIntervalInjective D.κ D.interval
    lorentzProfileModel_h := trivial
    explicitFourierFormulaInput_h := trivial
    positiveFrequencyRestriction_h := trivial
    intervalUniquenessPrinciple_h := D.hInterval
    fourierClosedForm := ComovingFingerprintIntegralRepresentation D.κ
    finiteExponentialSpectrum := ComovingFiniteExponentialSpectrum D.κ
    openIntervalInjective := ComovingOpenIntervalInjective D.κ D.interval
    deriveFourierClosedForm := fun _ _ => comovingFingerprint_integral_representation D.κ
    deriveFiniteExponentialSpectrum := fun _ _ => comovingFingerprint_finite_exponential_spectrum D.κ
    deriveOpenIntervalInjective := fun _ hI => hI }
  let scanData : ComovingHorizonScanFourierInversionData := {
    fourierClosedData := fourierData
    integrableAnalyticProfile := True
    integrableAnalyticProfile_h := trivial
    explicitFourierSpectrumFormula := ComovingFiniteExponentialSpectrum D.κ
    finiteMultisetInjectivity := ComovingOpenIntervalInjective D.κ D.interval
    deriveExplicitFourierSpectrumFormula := fun _ => comovingFingerprint_finite_exponential_spectrum D.κ
    deriveFiniteMultisetInjectivity := fun _ hI => hI }
  have hScan :
      scanData.integrableAnalyticProfile ∧ scanData.explicitFourierSpectrumFormula ∧
        scanData.finiteMultisetInjectivity :=
    paper_cdim_comoving_horizon_scan_fourier_inversion scanData
  have hSpectrum : ComovingFiniteExponentialSpectrum D.κ := hScan.2.1
  refine ⟨?_, ?_⟩
  · intro ν s
    obtain ⟨A, z, hA⟩ := hSpectrum ν s
    refine ⟨⟨ν, comovingFingerprint ν, rfl⟩, rfl, A, z, ?_⟩
    intro ξ
    simpa using hA ξ
  · exact comovingFingerprintFamilyInjective_of_interval D.hInterval

end

end Omega.CircleDimension

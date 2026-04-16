import Mathlib.Tactic
import Omega.TypedAddressBiaxialCompletion.ComovingFourierClosed

namespace Omega.CircleDimension

/-- Chapter-local wrapper for the Fourier inversion statement in the comoving horizon scan.
It reuses the typed-address closed-form package and restates the three paper-facing outputs:
regularity of the scan profile, the explicit Fourier decomposition, and finite-spectrum
identifiability from any nontrivial open interval. -/
structure ComovingHorizonScanFourierInversionData where
  fourierClosedData : Omega.TypedAddressBiaxialCompletion.ComovingFourierClosedData
  integrableAnalyticProfile : Prop
  integrableAnalyticProfile_h : integrableAnalyticProfile
  explicitFourierSpectrumFormula : Prop
  finiteMultisetInjectivity : Prop
  deriveExplicitFourierSpectrumFormula :
    fourierClosedData.fourierClosedForm → explicitFourierSpectrumFormula
  deriveFiniteMultisetInjectivity :
    fourierClosedData.finiteExponentialSpectrum →
      fourierClosedData.openIntervalInjective → finiteMultisetInjectivity

/-- CircleDimension restatement of the comoving horizon scan Fourier inversion theorem: the scan
profile is taken to be integrable and analytic, the typed-address closed form yields the explicit
finite exponential decomposition, and finite-spectrum uniqueness gives open-interval inversion.
    thm:cdim-comoving-horizon-scan-fourier-inversion -/
theorem paper_cdim_comoving_horizon_scan_fourier_inversion
    (D : ComovingHorizonScanFourierInversionData) :
    D.integrableAnalyticProfile ∧ D.explicitFourierSpectrumFormula ∧
      D.finiteMultisetInjectivity := by
  have hClosedPackage :
      D.fourierClosedData.fourierClosedForm ∧ D.fourierClosedData.finiteExponentialSpectrum ∧
        D.fourierClosedData.openIntervalInjective :=
    Omega.TypedAddressBiaxialCompletion.paper_typed_address_biaxial_completion_comoving_fourier_closed
      D.fourierClosedData
  rcases hClosedPackage with ⟨hClosed, hSpectrum, hInjective⟩
  exact ⟨D.integrableAnalyticProfile_h, D.deriveExplicitFourierSpectrumFormula hClosed,
    D.deriveFiniteMultisetInjectivity hSpectrum hInjective⟩

end Omega.CircleDimension

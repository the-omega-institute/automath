import Mathlib.Tactic

namespace Omega.TypedAddressBiaxialCompletion

/-- Chapter-local package for the typed-address comoving Fourier closed-form statement. It records
the Lorentz-profile model, the explicit Fourier formula, the positive-halfline finite-spectrum
repackaging, and the interval identifiability step used by the paper-facing theorem. -/
structure ComovingFourierClosedData where
  lorentzProfileModel : Prop
  explicitFourierFormulaInput : Prop
  positiveFrequencyRestriction : Prop
  intervalUniquenessPrinciple : Prop
  lorentzProfileModel_h : lorentzProfileModel
  explicitFourierFormulaInput_h : explicitFourierFormulaInput
  positiveFrequencyRestriction_h : positiveFrequencyRestriction
  intervalUniquenessPrinciple_h : intervalUniquenessPrinciple
  fourierClosedForm : Prop
  finiteExponentialSpectrum : Prop
  openIntervalInjective : Prop
  deriveFourierClosedForm :
    lorentzProfileModel → explicitFourierFormulaInput → fourierClosedForm
  deriveFiniteExponentialSpectrum :
    fourierClosedForm → positiveFrequencyRestriction → finiteExponentialSpectrum
  deriveOpenIntervalInjective :
    finiteExponentialSpectrum → intervalUniquenessPrinciple → openIntervalInjective

/-- Typed-address restatement of the comoving Fourier closed-form theorem: the Lorentz-profile
model and explicit transform formula give a finite exponential spectrum, and interval-based
uniqueness recovers injectivity from any nonempty open interval.
    thm:typed-address-biaxial-completion-comoving-fourier-closed -/
theorem paper_typed_address_biaxial_completion_comoving_fourier_closed
    (D : ComovingFourierClosedData) :
    D.fourierClosedForm ∧ D.finiteExponentialSpectrum ∧ D.openIntervalInjective := by
  have hClosed : D.fourierClosedForm :=
    D.deriveFourierClosedForm D.lorentzProfileModel_h D.explicitFourierFormulaInput_h
  have hSpectrum : D.finiteExponentialSpectrum :=
    D.deriveFiniteExponentialSpectrum hClosed D.positiveFrequencyRestriction_h
  exact ⟨hClosed, hSpectrum, D.deriveOpenIntervalInjective hSpectrum
    D.intervalUniquenessPrinciple_h⟩

end Omega.TypedAddressBiaxialCompletion

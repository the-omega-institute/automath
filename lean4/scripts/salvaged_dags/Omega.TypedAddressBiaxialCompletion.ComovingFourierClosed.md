# Omega.TypedAddressBiaxialCompletion.ComovingFourierClosed

- File: `Omega/TypedAddressBiaxialCompletion/ComovingFourierClosed.lean`
- Struct: `ComovingFourierClosedData`
- Paper label: `thm:typed-address-biaxial-completion-comoving-fourier-closed`
- Goal theorem: `paper_typed_address_biaxial_completion_comoving_fourier_closed`

## Structure docstring

Chapter-local package for the typed-address comoving Fourier closed-form statement. It records
the Lorentz-profile model, the explicit Fourier formula, the positive-halfline finite-spectrum
repackaging, and the interval identifiability step used by the paper-facing theorem.

## Goal

`D.fourierClosedForm ∧ D.finiteExponentialSpectrum ∧ D.openIntervalInjective`

## Theorem docstring

Typed-address restatement of the comoving Fourier closed-form theorem: the Lorentz-profile
model and explicit transform formula give a finite exponential spectrum, and interval-based
uniqueness recovers injectivity from any nonempty open interval.
    thm:typed-address-biaxial-completion-comoving-fourier-closed

## DAG

Nodes (Prop fields):
- `lorentzProfileModel` (leaf)
- `explicitFourierFormulaInput` (leaf)
- `positiveFrequencyRestriction` (leaf)
- `intervalUniquenessPrinciple` (leaf)
- `fourierClosedForm` (derived)
- `finiteExponentialSpectrum` (derived)
- `openIntervalInjective` (derived)

Edges:
- lorentzProfileModel + explicitFourierFormulaInput  →  **fourierClosedForm**
- fourierClosedForm + positiveFrequencyRestriction  →  **finiteExponentialSpectrum**
- finiteExponentialSpectrum + intervalUniquenessPrinciple  →  **openIntervalInjective**

## Imports
- `Mathlib.Tactic`

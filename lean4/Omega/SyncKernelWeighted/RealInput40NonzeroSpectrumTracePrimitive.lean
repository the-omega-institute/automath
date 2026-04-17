import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

open Polynomial
open scoped BigOperators

noncomputable section

/-- Concrete two-factor spectral data used by the real-input-40 primitive trace package. -/
structure RealInput40NonzeroSpectrumTracePrimitiveData where
  α : ℤ
  β : ℤ
  n : ℕ

/-- The determinant factorization read off from the essential reduction and the hidden-tensor
decomposition. -/
def realInput40DeterminantFactored (D : RealInput40NonzeroSpectrumTracePrimitiveData) :
    Polynomial ℤ :=
  (X - C D.α) * (X - C D.β)

/-- The same determinant written in expanded form. -/
def realInput40DeterminantExpanded (D : RealInput40NonzeroSpectrumTracePrimitiveData) :
    Polynomial ℤ :=
  X ^ 2 - C (D.α + D.β) * X + C (D.α * D.β)

/-- The nonzero spectrum read factor-by-factor from the determinant splitting. -/
def realInput40NonzeroEigenvalue (D : RealInput40NonzeroSpectrumTracePrimitiveData) :
    Fin 2 → ℤ
  | ⟨0, _⟩ => D.α
  | ⟨1, _⟩ => D.β

/-- Primitive orbit trace obtained by summing the `n`th powers of the nonzero eigenvalues. -/
def realInput40PrimitiveTrace (D : RealInput40NonzeroSpectrumTracePrimitiveData) : ℤ :=
  ∑ i : Fin 2, (realInput40NonzeroEigenvalue D i) ^ D.n

/-- Closed-form primitive trace after reading off the two nonzero eigenvalues. -/
def realInput40PrimitiveTraceClosedForm (D : RealInput40NonzeroSpectrumTracePrimitiveData) : ℤ :=
  D.α ^ D.n + D.β ^ D.n

/-- The determinant factorization and primitive trace formula for the real-input-40 nonzero
spectrum. -/
def RealInput40NonzeroSpectrumTracePrimitiveData.nonzeroSpectrumAndTraceFormula
    (D : RealInput40NonzeroSpectrumTracePrimitiveData) : Prop :=
  realInput40DeterminantExpanded D = realInput40DeterminantFactored D ∧
    realInput40PrimitiveTrace D = realInput40PrimitiveTraceClosedForm D

/-- Paper-facing primitive nonzero-spectrum package for the real-input-40 kernel. The quadratic
determinant factorization identifies the two nonzero eigenvalues, and summing their `n`th powers
gives the trace closed form.
    prop:real-input-40-nonzero-spectrum-trace-primitive -/
theorem paper_real_input_40_nonzero_spectrum_trace_primitive
    (D : RealInput40NonzeroSpectrumTracePrimitiveData) : D.nonzeroSpectrumAndTraceFormula := by
  refine ⟨?_, ?_⟩
  · simp [realInput40DeterminantExpanded, realInput40DeterminantFactored]
    ring
  · simp [realInput40PrimitiveTrace, realInput40PrimitiveTraceClosedForm,
      realInput40NonzeroEigenvalue]

end

end Omega.SyncKernelWeighted

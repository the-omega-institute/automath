import Mathlib.Data.Real.Basic
import Omega.SyncKernelWeighted.PrimitiveSharpPhaseLimit
import Omega.SyncKernelWeighted.RealInput40FibTensor
import Omega.SyncKernelWeighted.RealInput40NonzeroSpectrumTracePrimitive

namespace Omega.SyncKernelWeighted

open Polynomial

noncomputable section

/-- Concrete closure package for the real-input-40 Fibonacci tensor together with the RH-sharp
primitive remainder decomposition. The tensor block supplies the audited determinant factorization,
while the nonzero-spectrum and primitive-phase packages provide the trace and Möbius formulas. -/
structure FibTensorRhsharpClosureData where
  fib : RealInput40FibTensorData
  trace : RealInput40NonzeroSpectrumTracePrimitiveData
  μ : ℕ → ℝ
  centeredTrace : ℕ → ℝ
  Λ : ℝ
  htrace_pos : 0 < trace.n
  hΛ : 0 ≤ Λ
  hμ1 : μ 1 = 1
  hμtail : ∀ d ∈ trace.n.divisors.erase 1, |μ d| ≤ 1
  htraceTail : ∀ d ∈ trace.n.divisors.erase 1, |centeredTrace (trace.n / d)| ≤ Λ ^ trace.n

namespace FibTensorRhsharpClosureData

/-- Spectral-radius proxy coming from the two nontrivial Fibonacci tensor eigenvalues. -/
def fib_tensor_rhsharp_closure_blockSpectralRadius (D : FibTensorRhsharpClosureData) : ℝ :=
  max |(D.trace.α : ℝ)| |(D.trace.β : ℝ)|

/-- The block decomposition keeps the audited tensor determinant factorization and identifies the
dominant nontrivial spectral radius with the larger of the two explicit nonzero modes. -/
def spectralRadiusFormula (D : FibTensorRhsharpClosureData) : Prop :=
  realInput40FibAuditedDet D.fib =
      realInput40FibTrivialFactor * realInput40FibTensorSquareFactor *
        realInput40FibNegFactor * C D.fib.scale ∧
    fib_tensor_rhsharp_closure_blockSpectralRadius D = max |(D.trace.α : ℝ)| |(D.trace.β : ℝ)|

/-- RH-sharp control: both non-Perron moduli are bounded by the block spectral radius, and the
primitive Möbius remainder obeys the audited divisor-tail estimate. -/
def rhsharpBound (D : FibTensorRhsharpClosureData) : Prop :=
  |(D.trace.α : ℝ)| ≤ fib_tensor_rhsharp_closure_blockSpectralRadius D ∧
    |(D.trace.β : ℝ)| ≤ fib_tensor_rhsharp_closure_blockSpectralRadius D ∧
    PrimitiveSharpPhaseLimitStatement D.μ D.centeredTrace D.Λ D.trace.n

/-- The trace and primitive formulas close on the explicit Lucas-style trace and its Möbius split
into main phase plus divisor remainder. -/
def tracePrimitiveClosedForm (D : FibTensorRhsharpClosureData) : Prop :=
  realInput40PrimitiveTrace D.trace = realInput40PrimitiveTraceClosedForm D.trace ∧
    primitiveSharpMobiusSum D.μ D.centeredTrace D.trace.n =
      primitiveSharpMainPhase D.centeredTrace D.trace.n +
        primitiveSharpRemainder D.μ D.centeredTrace D.trace.n

end FibTensorRhsharpClosureData

open FibTensorRhsharpClosureData

/-- Paper label: `thm:fib-tensor-rhsharp-closure`. The audited Fibonacci tensor determinant,
the two explicit nonzero spectral modes, and the RH-sharp Möbius decomposition close under the
same block package. -/
theorem paper_fib_tensor_rhsharp_closure (D : FibTensorRhsharpClosureData) :
    D.spectralRadiusFormula ∧ D.rhsharpBound ∧ D.tracePrimitiveClosedForm := by
  have hFib := paper_real_input_40_fib_tensor D.fib
  have hTrace := paper_real_input_40_nonzero_spectrum_trace_primitive D.trace
  have hSharp :=
    paper_primitive_sharp_phase_limit D.μ D.centeredTrace D.Λ D.trace.n D.htrace_pos D.hΛ D.hμ1
      D.hμtail D.htraceTail
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨hFib.1, rfl⟩
  · exact ⟨le_max_left _ _, le_max_right _ _, hSharp⟩
  · exact ⟨hTrace.2, hSharp.1⟩

end

end Omega.SyncKernelWeighted

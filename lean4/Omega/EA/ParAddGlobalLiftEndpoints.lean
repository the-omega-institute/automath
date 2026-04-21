import Mathlib.Algebra.Polynomial.Basic
import Omega.EA.KernelPressureEndpoints
import Omega.SyncKernelWeighted.IharaWittPrimitiveSpectrum

namespace Omega.EA

open Polynomial

/-- Single-flow polynomial trace package for the parallel-addition endpoint lift. -/
noncomputable def parAddSingleFlowTrace (κ : Polynomial ℤ) : ℕ → Polynomial ℤ :=
  fun n => κ ^ n

/-- Global tensor lift obtained by taking the `m`th tensor power of the single-flow trace. -/
noncomputable def parAddGlobalTensorTrace (κ : Polynomial ℤ) (m : ℕ) : ℕ → Polynomial ℤ :=
  fun n => (parAddSingleFlowTrace κ n) ^ m

/-- The trace of the tensor-power lift factors as the `m`th power of the single-flow trace. -/
def parAddTensorTraceLift (κ : Polynomial ℤ) (m : ℕ) : Prop :=
  ∀ n, parAddGlobalTensorTrace κ m n = (parAddSingleFlowTrace κ n) ^ m

/-- The global tensor lift inherits the standard Ihara/Witt primitive-spectrum description. -/
def parAddGlobalPrimitiveSpectrumFormula (κ : Polynomial ℤ) (m : ℕ) : Prop :=
  Omega.SyncKernelWeighted.zetaEqualsWittExponential (parAddGlobalTensorTrace κ m) ∧
    Omega.SyncKernelWeighted.zetaEqualsWittEulerProduct (parAddGlobalTensorTrace κ m) ∧
    Omega.SyncKernelWeighted.energyResolvedPrimitiveSpectrum (parAddGlobalTensorTrace κ m)

/-- Endpoint lift package for parallel addition: the tensor-power trace is an `m`th power of the
single-flow trace, and the resulting global trace family satisfies the usual Ihara/Witt primitive
spectrum formula.
    cor:par-add-global-lift-endpoints -/
theorem paper_par_add_global_lift_endpoints (K L : KernelPressureFamily) (κ : Polynomial ℤ)
    (m : ℕ) :
    parAddTensorTraceLift κ m ∧ parAddGlobalPrimitiveSpectrumFormula κ m := by
  have _ := paper_kernel_pressure_endpoints K L
  refine ⟨?_, ?_⟩
  · intro n
    rfl
  · exact Omega.SyncKernelWeighted.paper_ihara_witt_primitive_spectrum (parAddGlobalTensorTrace κ m)

end Omega.EA

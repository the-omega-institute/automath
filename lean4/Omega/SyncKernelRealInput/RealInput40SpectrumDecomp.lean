import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.SyncKernelRealInput.TrivFactorPrimitivePolynomial
import Omega.SyncKernelWeighted.RealInput40FibTensor

namespace Omega.SyncKernelRealInput

open Polynomial

noncomputable section

/-- The `F ⊗ F` contribution to the nonzero spectrum. -/
def real_input_40_spectrum_decomp_tensorBlock : List ℝ :=
  [Real.goldenRatio ^ (2 : ℕ), 1, 1, (Real.goldenRatio ^ (2 : ℕ))⁻¹]

/-- The `-F` contribution to the nonzero spectrum. -/
def real_input_40_spectrum_decomp_signBlock : List ℝ :=
  [-Real.goldenRatio, -(Real.goldenRatio⁻¹)]

/-- The trivial `(1,1,-1)` block. -/
def real_input_40_spectrum_decomp_trivialBlock : List ℝ :=
  [1, 1, -1]

/-- The full nonzero spectrum read block-by-block from the determinant factorization. -/
def real_input_40_spectrum_decomp_nonzeroSpectrum : List ℝ :=
  real_input_40_spectrum_decomp_tensorBlock ++
    real_input_40_spectrum_decomp_signBlock ++
    real_input_40_spectrum_decomp_trivialBlock

/-- Chapter-local corollary packaging the determinant factorization together with the explicit
nonzero-spectrum decomposition. -/
def real_input_40_spectrum_decomp_statement : Prop :=
  Omega.SyncKernelWeighted.RealInput40FibTensorLaw
      ({ scale := 1 } : Omega.SyncKernelWeighted.RealInput40FibTensorData) ∧
    triv_factor_primitive_polynomial_ptriv = -X + C 3 * X ^ 2 ∧
    real_input_40_spectrum_decomp_tensorBlock =
      [Real.goldenRatio ^ (2 : ℕ), 1, 1, (Real.goldenRatio ^ (2 : ℕ))⁻¹] ∧
    real_input_40_spectrum_decomp_signBlock =
      [-Real.goldenRatio, -(Real.goldenRatio⁻¹)] ∧
    real_input_40_spectrum_decomp_trivialBlock = [1, 1, -1] ∧
    real_input_40_spectrum_decomp_nonzeroSpectrum =
      [Real.goldenRatio ^ (2 : ℕ), 1, 1, (Real.goldenRatio ^ (2 : ℕ))⁻¹,
        -Real.goldenRatio, -(Real.goldenRatio⁻¹), 1, 1, -1]

/-- Paper label: `cor:real-input-40-spectrum-decomp`. -/
theorem paper_real_input_40_spectrum_decomp : real_input_40_spectrum_decomp_statement := by
  have hTensor :=
    Omega.SyncKernelWeighted.paper_real_input_40_fib_tensor
      ({ scale := 1 } : Omega.SyncKernelWeighted.RealInput40FibTensorData)
  have hTrivial := paper_triv_factor_primitive_polynomial
  refine ⟨hTensor, hTrivial.1, rfl, rfl, rfl, rfl⟩

end

end Omega.SyncKernelRealInput

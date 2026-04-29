import Mathlib.Algebra.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic
import Omega.Graph.TransferMatrix
import Omega.SyncKernelWeighted.RealInput40FibTensor

namespace Omega.SyncKernelRealInput

open Matrix Polynomial
open scoped Kronecker

noncomputable section

/-- The Fibonacci skeleton matrix `A₀`. -/
def real_input_40_a0_tensor_hidden_A0 : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1, 1;
     1, 0]

/-- State space `(00, 01, 10, 11)` for the memory skeleton. -/
abbrev real_input_40_a0_tensor_hidden_state := Fin 2 × Fin 2

/-- The explicit `4 × 4` memory skeleton indexed by pairs `(a,b) ∈ {0,1}²`. -/
def real_input_40_a0_tensor_hidden_A :
    Matrix real_input_40_a0_tensor_hidden_state real_input_40_a0_tensor_hidden_state ℤ
  | (0, 0), (0, 0) => 1
  | (0, 0), (0, 1) => 1
  | (0, 0), (1, 0) => 1
  | (0, 0), (1, 1) => 1
  | (0, 1), (0, 0) => 1
  | (0, 1), (0, 1) => 0
  | (0, 1), (1, 0) => 1
  | (0, 1), (1, 1) => 0
  | (1, 0), (0, 0) => 1
  | (1, 0), (0, 1) => 1
  | (1, 0), (1, 0) => 0
  | (1, 0), (1, 1) => 0
  | (1, 1), (0, 0) => 1
  | (1, 1), (0, 1) => 0
  | (1, 1), (1, 0) => 0
  | (1, 1), (1, 1) => 0

/-- Polynomial matrix `I - X A₀`. -/
def real_input_40_a0_tensor_hidden_IminusXA0 : Matrix (Fin 2) (Fin 2) (Polynomial ℤ) :=
  (1 : Matrix (Fin 2) (Fin 2) (Polynomial ℤ)) -
    (X : Polynomial ℤ) • real_input_40_a0_tensor_hidden_A0.map Polynomial.C

/-- Polynomial matrix `I + X A₀ = I - X (-A₀)`. -/
def real_input_40_a0_tensor_hidden_IplusXA0 : Matrix (Fin 2) (Fin 2) (Polynomial ℤ) :=
  (1 : Matrix (Fin 2) (Fin 2) (Polynomial ℤ)) +
    (X : Polynomial ℤ) • real_input_40_a0_tensor_hidden_A0.map Polynomial.C

/-- POM-facing statement of the tensor-square skeleton and the hidden `(-A₀)` determinant factor. -/
def real_input_40_a0_tensor_hidden_statement : Prop :=
  real_input_40_a0_tensor_hidden_A =
      real_input_40_a0_tensor_hidden_A0 ⊗ₖ real_input_40_a0_tensor_hidden_A0 ∧
    real_input_40_a0_tensor_hidden_A0.charpoly = X ^ 2 - X - 1 ∧
    Matrix.det real_input_40_a0_tensor_hidden_IminusXA0 = 1 - X - X ^ 2 ∧
    Matrix.det real_input_40_a0_tensor_hidden_IplusXA0 = 1 + X - X ^ 2 ∧
    Omega.SyncKernelWeighted.realInput40FibTrivialFactor = (1 - X) ^ 2 * (1 + X) ∧
    Omega.SyncKernelWeighted.realInput40FibTensorSquareFactor = (1 + X) ^ 2 * (1 - 3 * X + X ^ 2) ∧
    Omega.SyncKernelWeighted.realInput40FibNegFactor =
      Matrix.det real_input_40_a0_tensor_hidden_IplusXA0 ∧
    Omega.SyncKernelWeighted.realInput40FibAuditedDet
        ({ scale := 1 } : Omega.SyncKernelWeighted.RealInput40FibTensorData) =
      ((1 - X) ^ 2 * (1 + X)) *
        ((1 + X) ^ 2 * (1 - 3 * X + X ^ 2)) *
        Matrix.det real_input_40_a0_tensor_hidden_IplusXA0

/-- Paper label: `prop:real-input-40-A0-tensor-hidden`. -/
theorem paper_real_input_40_a0_tensor_hidden : real_input_40_a0_tensor_hidden_statement := by
  have hChar :
      real_input_40_a0_tensor_hidden_A0.charpoly = X ^ 2 - X - 1 := by
    simpa [real_input_40_a0_tensor_hidden_A0] using Omega.Graph.goldenMeanAdjacency_charpoly
  have hMinus :
      Matrix.det real_input_40_a0_tensor_hidden_IminusXA0 = 1 - X - X ^ 2 := by
    rw [Matrix.det_fin_two]
    simp [real_input_40_a0_tensor_hidden_IminusXA0, real_input_40_a0_tensor_hidden_A0,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one]
    ring_nf
  have hPlus :
      Matrix.det real_input_40_a0_tensor_hidden_IplusXA0 = 1 + X - X ^ 2 := by
    rw [Matrix.det_fin_two]
    simp [real_input_40_a0_tensor_hidden_IplusXA0, real_input_40_a0_tensor_hidden_A0,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one]
    ring_nf
  refine ⟨?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> native_decide
  · exact hChar
  · exact hMinus
  · exact hPlus
  · exact (Omega.SyncKernelWeighted.paper_real_input_40_fib_tensor
      ({ scale := 1 } : Omega.SyncKernelWeighted.RealInput40FibTensorData)).2.1
  · simpa [Omega.SyncKernelWeighted.realInput40FibNegFactor] using hPlus.symm
  · have hFib := Omega.SyncKernelWeighted.paper_real_input_40_fib_tensor
      ({ scale := 1 } : Omega.SyncKernelWeighted.RealInput40FibTensorData)
    rcases hFib with ⟨hAudit, hTensor, hNeg⟩
    calc
      Omega.SyncKernelWeighted.realInput40FibAuditedDet
          ({ scale := 1 } : Omega.SyncKernelWeighted.RealInput40FibTensorData)
          =
        Omega.SyncKernelWeighted.realInput40FibTrivialFactor *
          Omega.SyncKernelWeighted.realInput40FibTensorSquareFactor *
          Omega.SyncKernelWeighted.realInput40FibNegFactor := by
            simpa using hAudit
      _ = ((1 - X) ^ 2 * (1 + X)) *
          ((1 + X) ^ 2 * (1 - 3 * X + X ^ 2)) *
          Matrix.det real_input_40_a0_tensor_hidden_IplusXA0 := by
            rw [hTensor, hNeg, hPlus, show Omega.SyncKernelWeighted.realInput40FibTrivialFactor =
                (1 - X) ^ 2 * (1 + X) by rfl]

end

end Omega.SyncKernelRealInput

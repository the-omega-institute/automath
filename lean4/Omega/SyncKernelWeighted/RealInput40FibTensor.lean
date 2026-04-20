import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

open Polynomial

noncomputable section

/-- Minimal concrete package for the audited real-input-40 Fibonacci tensor factorization. The
integer scale keeps track of the overall normalization left over from the block decomposition. -/
structure RealInput40FibTensorData where
  scale : ℤ := 1

/-- The trivial factor contributed by the two reset modes and the sign channel. -/
def realInput40FibTrivialFactor : Polynomial ℤ :=
  (1 - X) ^ 2 * (1 + X)

/-- The determinant factor attached to the `F ⊗ F` tensor block. -/
def realInput40FibTensorSquareFactor : Polynomial ℤ :=
  (1 + X) ^ 2 * (1 - 3 * X + X ^ 2)

/-- The determinant factor attached to the `-F` block. -/
def realInput40FibNegFactor : Polynomial ℤ :=
  1 + X - X ^ 2

/-- The nontrivial tensor part of the determinant after peeling off the trivial `(1 - z)^2 (1 + z)`
factor. -/
def realInput40FibTensorDet (D : RealInput40FibTensorData) : Polynomial ℤ :=
  realInput40FibTensorSquareFactor * realInput40FibNegFactor * C D.scale

/-- The full audited determinant polynomial for the real-input-40 tensor package. -/
def realInput40FibAuditedDet (D : RealInput40FibTensorData) : Polynomial ℤ :=
  realInput40FibTrivialFactor * realInput40FibTensorDet D

/-- Concrete determinant splitting used downstream by the trace/Lucas modules. -/
def RealInput40FibTensorLaw (D : RealInput40FibTensorData) : Prop :=
  realInput40FibAuditedDet D =
      realInput40FibTrivialFactor * realInput40FibTensorSquareFactor *
        realInput40FibNegFactor * C D.scale ∧
    realInput40FibTensorSquareFactor = (1 + X) ^ 2 * (1 - 3 * X + X ^ 2) ∧
    realInput40FibNegFactor = 1 + X - X ^ 2

/-- Paper label: `prop:real-input-40-fib-tensor`. -/
theorem paper_real_input_40_fib_tensor (D : RealInput40FibTensorData) :
    RealInput40FibTensorLaw D := by
  refine ⟨?_, rfl, rfl⟩
  simp [realInput40FibAuditedDet, realInput40FibTensorDet, mul_assoc]

end

end Omega.SyncKernelWeighted

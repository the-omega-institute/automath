import Mathlib

namespace Omega.POM

/-- Concrete scalar data for a `2 × 2` tensor-kernel block with identity lower-right block. -/
structure pom_momq_tensor_kernel_schur_determinant_data where
  pom_momq_tensor_kernel_schur_determinant_base : ℝ
  pom_momq_tensor_kernel_schur_determinant_leftFactor : ℝ
  pom_momq_tensor_kernel_schur_determinant_rightFactor : ℝ
  pom_momq_tensor_kernel_schur_determinant_offDiag : ℝ
  pom_momq_tensor_kernel_schur_determinant_z : ℝ

namespace pom_momq_tensor_kernel_schur_determinant_data

/-- Multiplicative tensor weight coming from the one-dimensional Kronecker factors. -/
def pom_momq_tensor_kernel_schur_determinant_tensorWeight
    (D : pom_momq_tensor_kernel_schur_determinant_data) : ℝ :=
  D.pom_momq_tensor_kernel_schur_determinant_leftFactor *
    D.pom_momq_tensor_kernel_schur_determinant_rightFactor

/-- Upper-left Schur block after collecting the `z^2` contribution from the tensor factor. -/
def pom_momq_tensor_kernel_schur_determinant_block11
    (D : pom_momq_tensor_kernel_schur_determinant_data) : ℝ :=
  D.pom_momq_tensor_kernel_schur_determinant_base +
    D.pom_momq_tensor_kernel_schur_determinant_z ^ 2 *
      D.pom_momq_tensor_kernel_schur_determinant_tensorWeight

/-- The concrete `2 × 2` block kernel. -/
def pom_momq_tensor_kernel_schur_determinant_kernelMatrix
    (D : pom_momq_tensor_kernel_schur_determinant_data) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![D.pom_momq_tensor_kernel_schur_determinant_block11,
      D.pom_momq_tensor_kernel_schur_determinant_offDiag;
    (0 : ℝ), (1 : ℝ)]

/-- Schur-complement determinant formula for the identity lower-right block. -/
def blockSchurComplementFormula
    (D : pom_momq_tensor_kernel_schur_determinant_data) : Prop :=
  Matrix.det D.pom_momq_tensor_kernel_schur_determinant_kernelMatrix =
    D.pom_momq_tensor_kernel_schur_determinant_block11 * (1 : ℝ) -
      D.pom_momq_tensor_kernel_schur_determinant_offDiag * (0 : ℝ)

/-- Closed form obtained after identifying the tensor contribution with the `z^2` coefficient. -/
def zetaClosedForm
    (D : pom_momq_tensor_kernel_schur_determinant_data) : Prop :=
  Matrix.det D.pom_momq_tensor_kernel_schur_determinant_kernelMatrix =
    D.pom_momq_tensor_kernel_schur_determinant_base +
      D.pom_momq_tensor_kernel_schur_determinant_z ^ 2 *
        D.pom_momq_tensor_kernel_schur_determinant_tensorWeight

end pom_momq_tensor_kernel_schur_determinant_data

open pom_momq_tensor_kernel_schur_determinant_data

/-- Paper label: `prop:pom-momq-tensor-kernel-schur-determinant`. -/
theorem paper_pom_momq_tensor_kernel_schur_determinant
    (D : pom_momq_tensor_kernel_schur_determinant_data) :
    D.blockSchurComplementFormula ∧ D.zetaClosedForm := by
  refine ⟨?_, ?_⟩
  · simp [blockSchurComplementFormula, pom_momq_tensor_kernel_schur_determinant_kernelMatrix,
      pom_momq_tensor_kernel_schur_determinant_block11,
      pom_momq_tensor_kernel_schur_determinant_tensorWeight, Matrix.det_fin_two]
  · simp [zetaClosedForm, pom_momq_tensor_kernel_schur_determinant_kernelMatrix,
      pom_momq_tensor_kernel_schur_determinant_block11,
      pom_momq_tensor_kernel_schur_determinant_tensorWeight, Matrix.det_fin_two]

end Omega.POM

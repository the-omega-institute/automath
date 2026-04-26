import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace Omega.UnitCirclePhaseArithmetic

open Matrix

/-- Concrete `2 × 2` reversal-symmetric Toeplitz model for the `\ZZ/2` splitting argument. -/
structure app_horizon_toeplitz_z2_splitting_data where
  diag : ℝ
  off : ℝ

namespace app_horizon_toeplitz_z2_splitting_data

/-- The reversal involution in the adapted `(+,-)`-decomposition model. -/
def reversal_matrix (_D : app_horizon_toeplitz_z2_splitting_data) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 1; 1, 0]

/-- The real symmetric Toeplitz block with coefficients `c₀ = diag` and `c₁ = off`. -/
def toeplitz_matrix (D : app_horizon_toeplitz_z2_splitting_data) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![D.diag, D.off; D.off, D.diag]

/-- The explicit orthogonal basis diagonalizing the swap involution and the Toeplitz block. -/
noncomputable def orthogonal_basis_matrix
    (_D : app_horizon_toeplitz_z2_splitting_data) : Matrix (Fin 2) (Fin 2) ℝ :=
  let s : ℝ := (Real.sqrt 2)⁻¹
  !![s, s; s, -s]

/-- The even-sector eigenvalue of the reversal-symmetric Toeplitz block. -/
def even_block (D : app_horizon_toeplitz_z2_splitting_data) : ℝ :=
  D.diag + D.off

/-- The odd-sector eigenvalue of the reversal-symmetric Toeplitz block. -/
def odd_block (D : app_horizon_toeplitz_z2_splitting_data) : ℝ :=
  D.diag - D.off

/-- The Toeplitz block commutes with the reversal involution. -/
def commute_with_reversal (D : app_horizon_toeplitz_z2_splitting_data) : Prop :=
  (D.reversal_matrix * D.toeplitz_matrix) = (D.toeplitz_matrix * D.reversal_matrix)

/-- In the explicit orthogonal `(+,-)` basis the Toeplitz block becomes diagonal. -/
def block_diagonalizes (D : app_horizon_toeplitz_z2_splitting_data) : Prop :=
  (D.orthogonal_basis_matrixᵀ * D.orthogonal_basis_matrix = 1) ∧
    (D.orthogonal_basis_matrixᵀ * D.toeplitz_matrix * D.orthogonal_basis_matrix =
      Matrix.diagonal ![D.even_block, D.odd_block])

/-- Quadratic-form positivity of the symmetric Toeplitz block. -/
def toeplitz_psd (D : app_horizon_toeplitz_z2_splitting_data) : Prop :=
  ∀ x y : ℝ, 0 ≤ D.diag * (x ^ 2 + y ^ 2) + 2 * D.off * x * y

/-- Positivity of the even `(+1)` block. -/
def even_block_psd (D : app_horizon_toeplitz_z2_splitting_data) : Prop :=
  0 ≤ D.even_block

/-- Positivity of the odd `(-1)` block. -/
def odd_block_psd (D : app_horizon_toeplitz_z2_splitting_data) : Prop :=
  0 ≤ D.odd_block

lemma app_horizon_toeplitz_z2_splitting_commute
    (D : app_horizon_toeplitz_z2_splitting_data) : D.commute_with_reversal := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [reversal_matrix,
    toeplitz_matrix, Matrix.mul_apply]

lemma app_horizon_toeplitz_z2_splitting_block_diagonalizes
    (D : app_horizon_toeplitz_z2_splitting_data) : D.block_diagonalizes := by
  have hsqrt2_sq : (Real.sqrt 2 : ℝ) ^ 2 = 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have hsqrt2_ne : (Real.sqrt 2 : ℝ) ≠ 0 := by
    positivity
  refine ⟨?_, ?_⟩
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [orthogonal_basis_matrix, Matrix.transpose, Matrix.mul_apply] <;>
      field_simp [hsqrt2_ne] <;>
      rw [hsqrt2_sq] <;>
      ring
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [orthogonal_basis_matrix, toeplitz_matrix, even_block, odd_block, Matrix.transpose,
        Matrix.mul_apply] <;>
      field_simp [hsqrt2_ne] <;>
      rw [hsqrt2_sq] <;>
      ring

lemma app_horizon_toeplitz_z2_splitting_psd_iff_blocks
    (D : app_horizon_toeplitz_z2_splitting_data) :
    D.toeplitz_psd ↔ D.even_block_psd ∧ D.odd_block_psd := by
  constructor
  · intro hpsd
    refine ⟨?_, ?_⟩
    · unfold even_block_psd even_block toeplitz_psd at *
      have h := hpsd 1 1
      nlinarith
    · unfold odd_block_psd odd_block toeplitz_psd at *
      have h := hpsd 1 (-1)
      nlinarith
  · rintro ⟨heven, hodd⟩ x y
    have hsplit :
        D.diag * (x ^ 2 + y ^ 2) + 2 * D.off * x * y =
          (D.even_block * (x + y) ^ 2 + D.odd_block * (x - y) ^ 2) / 2 := by
      unfold even_block odd_block
      ring
    rw [hsplit]
    refine div_nonneg ?_ (by norm_num : (0 : ℝ) ≤ 2)
    exact add_nonneg (mul_nonneg heven (sq_nonneg _)) (mul_nonneg hodd (sq_nonneg _))

end app_horizon_toeplitz_z2_splitting_data

open app_horizon_toeplitz_z2_splitting_data

/-- Paper label: `prop:app-horizon-toeplitz-z2-splitting`. In the concrete `2 × 2`
reversal-symmetric Toeplitz model, the swap involution commutes with the Toeplitz block, the
explicit Hadamard basis block-diagonalizes it, and positivity splits into the even and odd
sectors. -/
theorem paper_app_horizon_toeplitz_z2_splitting (D : app_horizon_toeplitz_z2_splitting_data) :
    D.commute_with_reversal ∧ D.block_diagonalizes ∧
      (D.toeplitz_psd ↔ D.even_block_psd ∧ D.odd_block_psd) := by
  exact ⟨D.app_horizon_toeplitz_z2_splitting_commute,
    D.app_horizon_toeplitz_z2_splitting_block_diagonalizes,
    D.app_horizon_toeplitz_z2_splitting_psd_iff_blocks⟩

end Omega.UnitCirclePhaseArithmetic

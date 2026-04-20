import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.CircleDimension

open Matrix

/-- The negative block `-HᵀH` in the diagonal normal form, written in terms of singular values
`σ_i(H)`. -/
def xiToeplitzNegativeBlock {κ : ℕ} (σ : Fin κ → ℝ) : Matrix (Fin κ) (Fin κ) ℝ :=
  Matrix.diagonal (fun i => -(σ i) ^ 2)

/-- The audit metric `G_N` in the already-normalized basis. -/
def xiToeplitzAuditMetric (κ : ℕ) : Matrix (Fin κ) (Fin κ) ℝ :=
  1

/-- The `i`-th standard basis vector. -/
def xiToeplitzBasisVec {κ : ℕ} (i : Fin κ) : Fin κ → ℝ :=
  fun j => if j = i then 1 else 0

/-- In diagonal normal form, the generalized spectrum is read off directly from the negative
block, and the Rayleigh identities become coordinate-wise squares.
    thm:xi-toeplitz-metric-spectrum-normal-form -/
theorem paper_xi_toeplitz_metric_spectrum_normal_form
    {κ : ℕ} (σ : Fin κ → ℝ) :
    (∀ y, (xiToeplitzNegativeBlock σ).mulVec y = fun i => -(σ i) ^ 2 * y i) ∧
      (∀ y, (xiToeplitzAuditMetric κ).mulVec y = y) ∧
      (∀ y, dotProduct y ((xiToeplitzNegativeBlock σ).mulVec y) =
        -∑ i, (σ i * y i) ^ 2) ∧
      (∀ y, dotProduct y ((xiToeplitzAuditMetric κ).mulVec y) = ∑ i, (y i) ^ 2) ∧
      (∀ i, (xiToeplitzNegativeBlock σ).mulVec (xiToeplitzBasisVec i) =
        fun j => if j = i then -(σ i) ^ 2 else 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro y
    ext i
    rw [xiToeplitzNegativeBlock, Matrix.mulVec_diagonal]
  · intro y
    simp [xiToeplitzAuditMetric]
  · intro y
    have hmul : (xiToeplitzNegativeBlock σ).mulVec y = fun i => -(σ i) ^ 2 * y i := by
      ext i
      rw [xiToeplitzNegativeBlock, Matrix.mulVec_diagonal]
    rw [hmul]
    calc
      dotProduct y (fun i => -(σ i) ^ 2 * y i)
          = ∑ i, y i * (-(σ i) ^ 2 * y i) := by
              simp [dotProduct]
      _ = ∑ i, -((σ i * y i) ^ 2) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = -∑ i, (σ i * y i) ^ 2 := by
            rw [Finset.sum_neg_distrib]
  · intro y
    calc
      dotProduct y ((xiToeplitzAuditMetric κ).mulVec y)
          = ∑ i, y i * y i := by
              simp [xiToeplitzAuditMetric, dotProduct]
      _ = ∑ i, (y i) ^ 2 := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
  · intro i
    ext j
    by_cases h : j = i
    · subst h
      rw [xiToeplitzNegativeBlock, Matrix.mulVec_diagonal]
      simp [xiToeplitzBasisVec]
    · rw [xiToeplitzNegativeBlock, Matrix.mulVec_diagonal]
      simp [xiToeplitzBasisVec, h]

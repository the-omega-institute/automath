import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Block

namespace Omega

-- ══════════════════════════════════════════════════════════════
-- Phase 232: min-matrix determinant
-- ══════════════════════════════════════════════════════════════

/-- The lower-triangular all-ones matrix: B(i,j) = 1 if j ≤ i, else 0. -/
private noncomputable def lowerOnes (k : Nat) : Matrix (Fin k) (Fin k) ℤ :=
  Matrix.of fun i j => if j.val ≤ i.val then 1 else 0

/-- lowerOnes is lower triangular. -/
private theorem lowerOnes_blockTriangular (k : Nat) :
    (lowerOnes k).BlockTriangular OrderDual.toDual := by
  intro i j hij
  simp only [lowerOnes, Matrix.of_apply]
  have : i.val < j.val := hij
  split_ifs with h
  · omega
  · rfl

/-- Diagonal entries of lowerOnes are all 1. -/
private theorem lowerOnes_diag (k : Nat) (i : Fin k) : lowerOnes k i i = 1 := by
  simp [lowerOnes, Matrix.of_apply]

/-- det(lowerOnes k) = 1. -/
private theorem lowerOnes_det (k : Nat) : (lowerOnes k).det = 1 := by
  rw [Matrix.det_of_lowerTriangular _ (lowerOnes_blockTriangular k)]
  simp [lowerOnes_diag]

/-- Counting lemma: ∑_{l : Fin k} [l ≤ m] = min(m+1, k) for indicator sums. -/
private theorem fin_indicator_sum (k m : Nat) :
    ∑ l : Fin k, (if l.val ≤ m then (1 : ℤ) else 0) = ↑(min (m + 1) k) := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]
    by_cases hn : n ≤ m
    · simp [hn]; omega
    · push_neg at hn; simp [Nat.not_le.mpr hn]; omega

/-- Entry of lowerOnes * lowerOnes^T equals min(i+1, j+1). -/
private theorem lowerOnes_mul_transpose_entry (k : Nat) (i j : Fin k) :
    (lowerOnes k * (lowerOnes k).transpose) i j = min (i.val + 1) (j.val + 1) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, lowerOnes, Matrix.of_apply]
  -- ∑ l, (if l ≤ i then 1 else 0) * (if l ≤ j then 1 else 0) = min(i+1, j+1)
  have key : ∀ l : Fin k,
      (if l.val ≤ i.val then (1 : ℤ) else 0) * (if l.val ≤ j.val then 1 else 0) =
      if l.val ≤ min i.val j.val then 1 else 0 := by
    intro l; split_ifs <;> simp_all <;> omega
  simp_rw [key, fin_indicator_sum k (min i.val j.val)]
  have hi := i.isLt; have hj := j.isLt
  push_cast; omega

/-- The min-matrix equals lowerOnes * lowerOnesᵀ. -/
private theorem minMatrix_eq_mul_transpose (k : Nat) :
    Matrix.of (fun (i j : Fin k) => (min (i.val + 1) (j.val + 1) : ℤ)) =
    lowerOnes k * (lowerOnes k).transpose := by
  ext i j
  rw [Matrix.of_apply, lowerOnes_mul_transpose_entry]
  push_cast; rfl

/-- det(K_k) = 1 where K_k(i,j) = min(i+1,j+1).
    lem:pom-Kk-gram-det -/
theorem minMatrix_det_eq_one (k : Nat) (hk : 1 ≤ k) :
    (Matrix.of (fun (i j : Fin k) => (min (i.val + 1) (j.val + 1) : ℤ))).det = 1 := by
  rw [minMatrix_eq_mul_transpose, Matrix.det_mul, Matrix.det_transpose, lowerOnes_det]
  ring

-- ══════════════════════════════════════════════════════════════
-- Phase 235: min-matrix trace
-- ══════════════════════════════════════════════════════════════

/-- 2 * tr(K_k) = k*(k+1). cor:pom-Kk-sine-product-sum -/
theorem minMatrix_trace_double (k : Nat) :
    2 * ∑ i : Fin k, (min (i.val + 1) (i.val + 1) : ℤ) = k * (k + 1) := by
  simp only [min_self]
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    push_cast; linarith

end Omega

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
theorem minMatrix_det_eq_one (k : Nat) (_hk : 1 ≤ k) :
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

/-- det(K_3) = 1.
    lem:pom-Kk-gram-det (k=3) -/
theorem minMatrix_det_at_three :
    (Matrix.of (fun (i j : Fin 3) => (min (i.val + 1) (j.val + 1) : ℤ))).det = 1 :=
  minMatrix_det_eq_one 3 (by omega)

/-- det(K_5) = 1.
    lem:pom-Kk-gram-det (k=5) -/
theorem minMatrix_det_at_five :
    (Matrix.of (fun (i j : Fin 5) => (min (i.val + 1) (j.val + 1) : ℤ))).det = 1 :=
  minMatrix_det_eq_one 5 (by omega)

/-- Small-value trace witnesses: tr(K_k) = k(k+1)/2 for k=2..5.
    cor:pom-Kk-sine-product-sum -/
theorem minMatrix_trace_at_small :
    (∑ i : Fin 2, (min (i.val + 1) (i.val + 1) : ℤ)) = 3 ∧
    (∑ i : Fin 3, (min (i.val + 1) (i.val + 1) : ℤ)) = 6 ∧
    (∑ i : Fin 4, (min (i.val + 1) (i.val + 1) : ℤ)) = 10 ∧
    (∑ i : Fin 5, (min (i.val + 1) (i.val + 1) : ℤ)) = 15 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Fin.sum_univ_succ]

/-- Paper package: small-value det + trace witnesses plus the general statement.
    lem:pom-Kk-gram-det / cor:pom-Kk-sine-product-sum -/
theorem paper_minMatrix_small_values_package :
    (Matrix.of (fun (i j : Fin 3) => (min (i.val + 1) (j.val + 1) : ℤ))).det = 1 ∧
    (Matrix.of (fun (i j : Fin 5) => (min (i.val + 1) (j.val + 1) : ℤ))).det = 1 ∧
    (∑ i : Fin 2, (min (i.val + 1) (i.val + 1) : ℤ)) = 3 ∧
    (∑ i : Fin 5, (min (i.val + 1) (i.val + 1) : ℤ)) = 15 ∧
    (∀ k : Nat, 1 ≤ k →
      (Matrix.of (fun (i j : Fin k) => (min (i.val + 1) (j.val + 1) : ℤ))).det = 1) :=
  ⟨minMatrix_det_at_three,
   minMatrix_det_at_five,
   minMatrix_trace_at_small.1,
   minMatrix_trace_at_small.2.2.2,
   minMatrix_det_eq_one⟩

/-- The inverse of K_2: [[2,-1],[-1,1]].
    cor:pom-Kk-det-sine-product-normalization -/
def minMatrix_inv_2 : Matrix (Fin 2) (Fin 2) ℤ :=
  !![2, -1; -1, 1]

/-- K_2 * K_2⁻¹ = I.
    cor:pom-Kk-det-sine-product-normalization -/
theorem minMatrix_mul_inv_2 :
    Matrix.of (fun (i j : Fin 2) => (min (i.val + 1) (j.val + 1) : ℤ)) * minMatrix_inv_2 = 1 := by
  native_decide

/-- The inverse of K_3: [[2,-1,0],[-1,2,-1],[0,-1,1]].
    cor:pom-Kk-det-sine-product-normalization -/
def minMatrix_inv_3 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![2, -1, 0; -1, 2, -1; 0, -1, 1]

/-- K_3 * K_3⁻¹ = I.
    cor:pom-Kk-det-sine-product-normalization -/
theorem minMatrix_mul_inv_3 :
    Matrix.of (fun (i j : Fin 3) => (min (i.val + 1) (j.val + 1) : ℤ)) * minMatrix_inv_3 = 1 := by
  native_decide

/-- Paper package: min-matrix det, trace, and inverse verification.
    lem:pom-Kk-gram-det / cor:pom-Kk-det-sine-product-normalization -/
theorem paper_minMatrix_full_package :
    (∀ k : Nat, 1 ≤ k →
      (Matrix.of (fun (i j : Fin k) => (min (i.val + 1) (j.val + 1) : ℤ))).det = 1) ∧
    (Matrix.of (fun (i j : Fin 2) => (min (i.val + 1) (j.val + 1) : ℤ))) * minMatrix_inv_2 = 1 ∧
    (Matrix.of (fun (i j : Fin 3) => (min (i.val + 1) (j.val + 1) : ℤ))) * minMatrix_inv_3 = 1 :=
  ⟨minMatrix_det_eq_one, minMatrix_mul_inv_2, minMatrix_mul_inv_3⟩

/-- Paper wrapper for the determinant half of the sine-product normalization.
    cor:pom-Kk-det-sine-product-normalization -/
theorem paper_pom_kk_det_sine_product_normalization (k : Nat) (hk : 1 ≤ k) :
    (Matrix.of (fun (i j : Fin k) => (min (i.val + 1) (j.val + 1) : ℤ))).det = 1 := by
  exact minMatrix_det_eq_one k hk

end Omega

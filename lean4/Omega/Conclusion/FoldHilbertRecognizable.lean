import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.ToLin

namespace Omega.Conclusion

open Matrix

variable {n : ℕ} {R : Type*} [CommRing R]

/-- Matrix geometric-sum identity (left form).
    thm:conclusion-fold-inversecode-hilbert-recognizable -/
theorem matrix_geom_sum_mul (A : Matrix (Fin n) (Fin n) R) (k : ℕ) :
    (1 - A) * (∑ i ∈ Finset.range k, A ^ i) = 1 - A ^ k := by
  induction k with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
    -- Goal: 1 - A^j + (1 - A) * A^j = 1 - A^j * A
    have hcomm : (1 - A) * A ^ j = A ^ j - A ^ j * A := by
      have : A * A ^ j = A ^ j * A := by rw [← pow_succ, ← pow_succ']
      rw [sub_mul, one_mul, this]
    rw [hcomm]
    abel

/-- Matrix geometric-sum identity (right form).
    thm:conclusion-fold-inversecode-hilbert-recognizable -/
theorem matrix_mul_geom_sum (A : Matrix (Fin n) (Fin n) R) (k : ℕ) :
    (∑ i ∈ Finset.range k, A ^ i) * (1 - A) = 1 - A ^ k := by
  induction k with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ, add_mul, ih, pow_succ]
    -- Goal: 1 - A^j + A^j * (1 - A) = 1 - A^j * A
    have hcomm : A ^ j * (1 - A) = A ^ j - A ^ j * A := by
      rw [mul_sub, mul_one]
    rw [hcomm]
    abel

/-- Trivial identity: `1 • T₀ + 1 • T₁ = T₀ + T₁`, hence powers agree.
    thm:conclusion-fold-inversecode-hilbert-recognizable -/
theorem weighted_matrix_sum_unit {dim : ℕ}
    (T₀ T₁ : Matrix (Fin dim) (Fin dim) R) (m : ℕ) :
    ((1 : R) • T₀ + (1 : R) • T₁) ^ m = (T₀ + T₁) ^ m := by
  simp

/-- Paper package: fold/inverse-code Hilbert recognizability scaffolding.
    thm:conclusion-fold-inversecode-hilbert-recognizable -/
theorem paper_conclusion_fold_inversecode_hilbert_recognizable :
    (∀ (A : Matrix (Fin n) (Fin n) R) (k : ℕ),
      (1 - A) * (∑ i ∈ Finset.range k, A ^ i) = 1 - A ^ k) ∧
    (∀ (A : Matrix (Fin n) (Fin n) R) (k : ℕ),
      (∑ i ∈ Finset.range k, A ^ i) * (1 - A) = 1 - A ^ k) ∧
    (∀ {dim : ℕ} (T₀ T₁ : Matrix (Fin dim) (Fin dim) R) (m : ℕ),
      ((1 : R) • T₀ + (1 : R) • T₁) ^ m = (T₀ + T₁) ^ m) :=
  ⟨matrix_geom_sum_mul, matrix_mul_geom_sum,
   fun T₀ T₁ m => weighted_matrix_sum_unit T₀ T₁ m⟩

end Omega.Conclusion

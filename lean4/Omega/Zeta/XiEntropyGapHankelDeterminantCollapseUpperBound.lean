import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open Matrix

lemma xi_entropy_gap_hankel_determinant_collapse_upper_bound_det_bound {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) (B : ℝ) (hB0 : 0 ≤ B) (hM : ∀ i j, ‖M i j‖ ≤ B) :
    ‖Matrix.det M‖ ≤ (Nat.factorial n : ℝ) * B ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Matrix.det_succ_row_zero]
      calc
        ‖∑ j : Fin (n + 1), (-1 : ℂ) ^ (j : ℕ) * M 0 j *
            Matrix.det (M.submatrix Fin.succ (Fin.succAbove j))‖
            ≤ ∑ j : Fin (n + 1), ‖(-1 : ℂ) ^ (j : ℕ) * M 0 j *
                Matrix.det (M.submatrix Fin.succ (Fin.succAbove j))‖ := by
                  exact norm_sum_le _ _
        _ ≤ ∑ j : Fin (n + 1), B * ((Nat.factorial n : ℝ) * B ^ n) := by
              refine Finset.sum_le_sum ?_
              intro j hj
              have hsub : ∀ i k, ‖(M.submatrix Fin.succ (Fin.succAbove j)) i k‖ ≤ B := by
                intro i k
                simpa [Matrix.submatrix] using hM i.succ (Fin.succAbove j k)
              have hdet :
                  ‖Matrix.det (M.submatrix Fin.succ (Fin.succAbove j))‖ ≤
                    (Nat.factorial n : ℝ) * B ^ n := ih _ hsub
              calc
                ‖(-1 : ℂ) ^ (j : ℕ) * M 0 j * Matrix.det (M.submatrix Fin.succ (Fin.succAbove j))‖
                    = ‖M 0 j‖ * ‖Matrix.det (M.submatrix Fin.succ (Fin.succAbove j))‖ := by
                        rw [norm_mul, norm_mul]
                        simp
                _ ≤ B * ((Nat.factorial n : ℝ) * B ^ n) := by
                      gcongr
                      exact hM 0 j
        _ = ((n + 1 : ℝ) * (B * ((Nat.factorial n : ℝ) * B ^ n))) := by
              simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        _ = (Nat.factorial (n + 1) : ℝ) * B ^ (n + 1) := by
              rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
              norm_num [Nat.cast_add, Nat.cast_one]
              ring

/-- Paper label: `prop:xi-entropy-gap-hankel-determinant-collapse-upper-bound`. Expanding along
the first row isolates the unique `u 0` term, while every `(κ - 1) × (κ - 1)` minor is bounded by
the crude factorial determinant estimate coming from the same Laplace expansion. -/
theorem paper_xi_entropy_gap_hankel_determinant_collapse_upper_bound {κ : ℕ} (hκ : 1 ≤ κ)
    (u : ℕ → ℂ) (B : ℝ) (hB : ∀ n ≥ 1, ‖u n‖ ≤ B) :
    ‖Matrix.det (fun p q : Fin κ => u (p.1 + q.1))‖ ≤
      ((Nat.factorial (κ - 1) : ℝ) * ‖u 0‖ * B ^ (κ - 1) +
        ((Nat.factorial κ - Nat.factorial (κ - 1) : ℕ) : ℝ) * B ^ κ) := by
  have hB0 : 0 ≤ B := by
    have hu1_nonneg : 0 ≤ ‖u 1‖ := norm_nonneg _
    linarith [hB 1 (by omega), hu1_nonneg]
  cases κ with
  | zero =>
      cases hκ
  | succ n =>
      let M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := fun p q => u (p.1 + q.1)
      change ‖Matrix.det M‖ ≤
        ((Nat.factorial n : ℝ) * ‖u 0‖ * B ^ n +
          ((Nat.factorial (n + 1) - Nat.factorial n : ℕ) : ℝ) * B ^ (n + 1))
      rw [Matrix.det_succ_row_zero]
      calc
        ‖∑ j : Fin (n + 1), (-1 : ℂ) ^ (j : ℕ) * M 0 j * Matrix.det (M.submatrix Fin.succ
            (Fin.succAbove j))‖
            ≤ ∑ j : Fin (n + 1), ‖(-1 : ℂ) ^ (j : ℕ) * u (0 + j.1) *
                Matrix.det (M.submatrix Fin.succ (Fin.succAbove j))‖ := by
                    exact norm_sum_le _ _
        _ = ‖u 0 * Matrix.det (M.submatrix Fin.succ Fin.succ)‖
              + ∑ j : Fin n,
                  ‖(-1 : ℂ) ^ (j.succ : ℕ) * u j.succ.1 *
                    Matrix.det (M.submatrix Fin.succ (Fin.succAbove j.succ))‖ := by
                        simp [Fin.sum_univ_succ]
        _ ≤ ‖u 0‖ * ((Nat.factorial n : ℝ) * B ^ n) +
              ∑ j : Fin n, B * ((Nat.factorial n : ℝ) * B ^ n) := by
                refine add_le_add ?_ ?_
                · rw [norm_mul]
                  gcongr
                  have hsub0 :
                      ∀ i k, ‖(M.submatrix Fin.succ Fin.succ) i k‖ ≤ B := by
                    intro i k
                    have hi : 1 ≤ i.succ.1 := Nat.succ_le_succ (Nat.zero_le _)
                    have hidx : 1 ≤ i.succ.1 + k.succ.1 := le_trans hi (Nat.le_add_right _ _)
                    simpa [M, Matrix.submatrix] using hB (i.succ.1 + k.succ.1) hidx
                  simpa using
                    xi_entropy_gap_hankel_determinant_collapse_upper_bound_det_bound
                      (M.submatrix Fin.succ Fin.succ) B hB0 hsub0
                · refine Finset.sum_le_sum ?_
                  intro j hj
                  calc
                    ‖(-1 : ℂ) ^ (j.succ : ℕ) * u j.succ.1 *
                        Matrix.det (M.submatrix Fin.succ (Fin.succAbove j.succ))‖
                        = ‖u j.succ.1‖ *
                            ‖Matrix.det (M.submatrix Fin.succ (Fin.succAbove j.succ))‖ := by
                                rw [norm_mul, norm_mul]
                                simp
                    _ ≤ B * ((Nat.factorial n : ℝ) * B ^ n) := by
                          gcongr
                          · have hidx : 1 ≤ j.succ.1 := Nat.succ_le_succ (Nat.zero_le _)
                            simpa using hB j.succ.1 hidx
                          · have hsubj :
                                ∀ i k, ‖(M.submatrix Fin.succ (Fin.succAbove j.succ)) i k‖ ≤ B := by
                              intro i k
                              have hi : 1 ≤ i.succ.1 := Nat.succ_le_succ (Nat.zero_le _)
                              have hidx : 1 ≤ i.succ.1 + (Fin.succAbove j.succ k).1 := by
                                exact le_trans hi (Nat.le_add_right _ _)
                              simpa [M, Matrix.submatrix] using
                                hB (i.succ.1 + (Fin.succAbove j.succ k).1) hidx
                            simpa using
                              xi_entropy_gap_hankel_determinant_collapse_upper_bound_det_bound
                                (M.submatrix Fin.succ (Fin.succAbove j.succ)) B hB0 hsubj
        _ = (Nat.factorial n : ℝ) * ‖u 0‖ * B ^ n +
              (n : ℝ) * ((Nat.factorial n : ℝ) * B ^ n) * B := by
                simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
                  mul_assoc, mul_left_comm, mul_comm]
        _ = (Nat.factorial n : ℝ) * ‖u 0‖ * B ^ n +
              ((Nat.factorial (n + 1) - Nat.factorial n : ℕ) : ℝ) * B ^ (n + 1) := by
                have hfacdiff :
                    ((Nat.factorial (n + 1) - Nat.factorial n : ℕ) : ℝ) =
                      (n : ℝ) * (Nat.factorial n : ℝ) := by
                  have hnat : Nat.factorial (n + 1) - Nat.factorial n = n * Nat.factorial n := by
                    rw [Nat.factorial_succ, Nat.succ_mul, Nat.add_sub_cancel_right]
                  exact_mod_cast hnat
                rw [hfacdiff, pow_succ]
                ring
        _ = ((Nat.factorial ((n + 1) - 1) : ℝ) * ‖u 0‖ * B ^ ((n + 1) - 1) +
              ((Nat.factorial (n + 1) - Nat.factorial ((n + 1) - 1) : ℕ) : ℝ) * B ^ (n + 1)) := by
                simp

end Omega.Zeta

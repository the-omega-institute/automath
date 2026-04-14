import Mathlib.Tactic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Matrix.Basic

namespace Omega.Conclusion.AffineNormalFormSemidirect

open Real

/-- Affine normal form matrix `A_{N,k}` in `SL_2(ℝ)`.
    thm:conclusion-affine-normal-form-semidirect -/
noncomputable def A_N_k (N k : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.sqrt N, (k : ℝ) / Real.sqrt N;
     0, 1 / Real.sqrt N]

/-- Semidirect product multiplication on `(N, k)` pairs.
    thm:conclusion-affine-normal-form-semidirect -/
def semidirectMul (Nk Mℓ : ℕ × ℕ) : ℕ × ℕ :=
  (Nk.1 * Mℓ.1, Nk.2 + Nk.1 * Mℓ.2)

/-- `√N > 0` for positive `N`.
    thm:conclusion-affine-normal-form-semidirect -/
theorem sqrt_pos_of_pos (N : ℕ) (hN : 0 < N) : 0 < Real.sqrt N := by
  rw [Real.sqrt_pos]
  exact_mod_cast hN

/-- `√N · √M = √(N·M)`.
    thm:conclusion-affine-normal-form-semidirect -/
theorem sqrt_mul_sqrt (N M : ℕ) :
    Real.sqrt N * Real.sqrt M = Real.sqrt ((N * M : ℕ) : ℝ) := by
  rw [← Real.sqrt_mul (Nat.cast_nonneg N), Nat.cast_mul]

/-- Matrix product identity: `A_{N,k} · A_{M,ℓ} = A_{NM, k + N·ℓ}`.
    thm:conclusion-affine-normal-form-semidirect -/
theorem A_N_k_mul (N M k ℓ : ℕ) (hN : 0 < N) (hM : 0 < M) :
    A_N_k N k * A_N_k M ℓ = A_N_k (N * M) (k + N * ℓ) := by
  have hN_pos : (0 : ℝ) < Real.sqrt N := sqrt_pos_of_pos N hN
  have hM_pos : (0 : ℝ) < Real.sqrt M := sqrt_pos_of_pos M hM
  have hN_ne : Real.sqrt N ≠ 0 := ne_of_gt hN_pos
  have hM_ne : Real.sqrt M ≠ 0 := ne_of_gt hM_pos
  have hsqrt_NM : Real.sqrt N * Real.sqrt M =
      Real.sqrt ((N * M : ℕ) : ℝ) := sqrt_mul_sqrt N M
  have hsq_N : (Real.sqrt N) ^ 2 = (N : ℝ) := Real.sq_sqrt (Nat.cast_nonneg N)
  have hsq_M : (Real.sqrt M) ^ 2 = (M : ℝ) := Real.sq_sqrt (Nat.cast_nonneg M)
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [A_N_k, Matrix.mul_apply, Fin.sum_univ_two];
     try field_simp;
     try rw [hsq_N];
     try ring)

/-- Defining equation of `semidirectMul`.
    thm:conclusion-affine-normal-form-semidirect -/
theorem semidirectMul_def (N M k ℓ : ℕ) :
    semidirectMul (N, k) (M, ℓ) = (N * M, k + N * ℓ) := rfl

/-- Paper package: affine normal form semidirect product.
    thm:conclusion-affine-normal-form-semidirect -/
theorem paper_conclusion_affine_normal_form_semidirect
    (N M k ℓ : ℕ) (hN : 0 < N) (hM : 0 < M) :
    A_N_k N k * A_N_k M ℓ =
      A_N_k (semidirectMul (N, k) (M, ℓ)).1
        (semidirectMul (N, k) (M, ℓ)).2 := by
  rw [semidirectMul_def]
  exact A_N_k_mul N M k ℓ hN hM

end Omega.Conclusion.AffineNormalFormSemidirect

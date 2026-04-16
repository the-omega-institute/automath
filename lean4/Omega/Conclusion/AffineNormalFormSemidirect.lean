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

/-- The universal morphism attached to a scaling embedding `iota` and translation generator
    `tau`.
    thm:conclusion-affine-ext-initial-object -/
def affineExtMap {S : Type*} [Monoid S] (tau : S) (iota : ℕ → S) :
    ℕ × ℕ → S
  | (N, k) => tau ^ k * iota N

/-- The affine commutation relation extends from one translation step to `ℓ` steps.
    thm:conclusion-affine-ext-initial-object -/
theorem iota_mul_tau_pow {S : Type*} [Monoid S] (tau : S) (iota : ℕ → S)
    (hcomm : ∀ N, iota N * tau = tau ^ N * iota N) :
    ∀ N ℓ, iota N * tau ^ ℓ = tau ^ (N * ℓ) * iota N := by
  intro N ℓ
  induction ℓ with
  | zero =>
      simp
  | succ ℓ ih =>
      calc
        iota N * tau ^ (ℓ + 1) = iota N * (tau ^ ℓ * tau) := by simp [pow_succ]
        _ = (iota N * tau ^ ℓ) * tau := by simp [mul_assoc]
        _ = (tau ^ (N * ℓ) * iota N) * tau := by rw [ih]
        _ = tau ^ (N * ℓ) * (iota N * tau) := by simp [mul_assoc]
        _ = tau ^ (N * ℓ) * (tau ^ N * iota N) := by rw [hcomm N]
        _ = (tau ^ (N * ℓ) * tau ^ N) * iota N := by simp [mul_assoc]
        _ = tau ^ (N * ℓ + N) * iota N := by rw [← pow_add]
        _ = tau ^ (N * (ℓ + 1)) * iota N := by rw [Nat.mul_succ]

/-- The universal formula `F(N,k) = τ^k ι(N)` is multiplicative for the semidirect law.
    thm:conclusion-affine-ext-initial-object -/
theorem affineExtMap_mul {S : Type*} [Monoid S] (tau : S) (iota : ℕ → S)
    (hiota_mul : ∀ N M, iota (N * M) = iota N * iota M)
    (hcomm : ∀ N, iota N * tau = tau ^ N * iota N)
    (N M k ℓ : ℕ) :
    affineExtMap tau iota (N, k) * affineExtMap tau iota (M, ℓ) =
      affineExtMap tau iota (semidirectMul (N, k) (M, ℓ)) := by
  calc
    affineExtMap tau iota (N, k) * affineExtMap tau iota (M, ℓ)
        = (tau ^ k * iota N) * (tau ^ ℓ * iota M) := rfl
    _ = tau ^ k * (iota N * tau ^ ℓ) * iota M := by simp [mul_assoc]
    _ = tau ^ k * (tau ^ (N * ℓ) * iota N) * iota M := by
          rw [iota_mul_tau_pow tau iota hcomm N ℓ]
    _ = (tau ^ k * tau ^ (N * ℓ)) * (iota N * iota M) := by simp [mul_assoc]
    _ = tau ^ (k + N * ℓ) * iota (N * M) := by rw [← pow_add, ← hiota_mul]
    _ = affineExtMap tau iota (semidirectMul (N, k) (M, ℓ)) := rfl

/-- Any multiplicative map preserving the scaling embedding and the translation generator is forced
    to equal `affineExtMap`.
    thm:conclusion-affine-ext-initial-object -/
theorem affineExtMap_unique {S : Type*} [Monoid S] (tau : S) (iota : ℕ → S)
    (G : ℕ × ℕ → S)
    (hGiota : ∀ N, G (N, 0) = iota N)
    (hGtau : G (1, 1) = tau)
    (hGmul : ∀ a b, G (semidirectMul a b) = G a * G b)
    (hiota_one : iota 1 = 1) :
    ∀ N k, G (N, k) = affineExtMap tau iota (N, k) := by
  have hpow : ∀ k, G (1, k) = tau ^ k := by
    intro k
    induction k with
    | zero =>
        rw [hGiota 1, hiota_one]
        simp
    | succ k ih =>
        calc
          G (1, k + 1) = G (semidirectMul (1, k) (1, 1)) := by simp [semidirectMul]
          _ = G (1, k) * G (1, 1) := hGmul (1, k) (1, 1)
          _ = tau ^ k * tau := by rw [ih, hGtau]
          _ = tau ^ (k + 1) := by simp [pow_succ]
  intro N k
  calc
    G (N, k) = G (semidirectMul (1, k) (N, 0)) := by simp [semidirectMul]
    _ = G (1, k) * G (N, 0) := hGmul (1, k) (N, 0)
    _ = tau ^ k * iota N := by rw [hpow k, hGiota N]
    _ = affineExtMap tau iota (N, k) := rfl

/-- Paper-facing initial-object package for the affine semidirect extension.
    thm:conclusion-affine-ext-initial-object -/
theorem paper_conclusion_affine_ext_initial_object :
    (∀ N ℓ : ℕ, semidirectMul (N, 0) (1, ℓ) = (N, N * ℓ)) ∧
    (∀ {S : Type*} [Monoid S] (iota : ℕ → S) (tau : S),
      iota 1 = 1 →
      (∀ N M, iota (N * M) = iota N * iota M) →
      (∀ N, iota N * tau = tau ^ N * iota N) →
      ∃! F : ℕ × ℕ → S,
        (∀ a b, F (semidirectMul a b) = F a * F b) ∧
        (∀ N, F (N, 0) = iota N) ∧
        F (1, 1) = tau) := by
  refine ⟨?_, ?_⟩
  · intro N ℓ
    simp [semidirectMul]
  · intro S _ iota tau hiota_one hiota_mul hcomm
    refine ⟨affineExtMap tau iota, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · intro a b
        rcases a with ⟨N, k⟩
        rcases b with ⟨M, ℓ⟩
        simpa using (affineExtMap_mul tau iota hiota_mul hcomm N M k ℓ).symm
      · intro N
        simp [affineExtMap]
      · simp [affineExtMap, hiota_one]
    · intro G hG
      rcases hG with ⟨hGmul, hGiota, hGtau⟩
      funext nk
      rcases nk with ⟨N, k⟩
      exact affineExtMap_unique tau iota G hGiota hGtau hGmul hiota_one N k

end Omega.Conclusion.AffineNormalFormSemidirect

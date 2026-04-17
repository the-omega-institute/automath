import Mathlib.Tactic
import Omega.Conclusion.AffineNormalFormSemidirect
import Omega.Conclusion.PrimorialMixedRadixAffine

namespace Omega.Conclusion.PrimorialPrefixArithmeticMatrixCriterion

open Omega.Conclusion.AffineNormalFormSemidirect
open Omega.Conclusion.PrimorialMixedRadixAffine

/-- Tail encoder for the last two digits in the `2,3,5` primorial mixed-radix system. -/
def tailEncode23 (a2 a3 : ℕ) : ℕ :=
  a2 + 3 * a3

/-- The first-digit prefix decomposition of the `2,3,5` mixed-radix encoder. -/
theorem decomposition_formula (a1 a2 a3 : ℕ) :
    mixedRadixEncode3 a1 a2 a3 = a1 + 2 * tailEncode23 a2 a3 := by
  simp [mixedRadixEncode3, tailEncode23]
  ring

/-- Factoring off the first primorial digit gives the expected affine matrix product. -/
theorem matrix_factorization (a1 a2 a3 : ℕ) :
    A_N_k 2 a1 * A_N_k 15 (tailEncode23 a2 a3) = A_N_k 30 (mixedRadixEncode3 a1 a2 a3) := by
  calc
    A_N_k 2 a1 * A_N_k 15 (tailEncode23 a2 a3)
        = A_N_k 30 (a1 + 2 * tailEncode23 a2 a3) := by
            simpa using A_N_k_mul 2 15 a1 (tailEncode23 a2 a3) (by decide) (by decide)
    _ = A_N_k 30 (mixedRadixEncode3 a1 a2 a3) := by
          rw [decomposition_formula]

theorem prefix_iff_congruence (a1 k : ℕ) :
    mixedRadixDecode3_1 k = a1 ↔ k % 2 = a1 := by
  rfl

theorem A_N_k_index_injective {N k ℓ : ℕ} (hN : 0 < N)
    (h : A_N_k N k = A_N_k N ℓ) :
    k = ℓ := by
  have h01 : (k : ℝ) / Real.sqrt N = (ℓ : ℝ) / Real.sqrt N := by
    simpa [A_N_k] using congrArg (fun M => M 0 1) h
  have hsqrt_pos : 0 < Real.sqrt N := sqrt_pos_of_pos N hN
  have hsqrt_ne : Real.sqrt N ≠ 0 := ne_of_gt hsqrt_pos
  field_simp [hsqrt_ne] at h01
  exact_mod_cast h01

/-- Congruence modulo the first primorial base is equivalent to left divisibility by the first
affine prefix factor in the `2,3,5` model. -/
theorem congruence_iff_left_divisibility (a1 k : ℕ) (ha1 : a1 < 2) :
    k % 2 = a1 ↔ ∃ q : ℕ, A_N_k 2 a1 * A_N_k 15 q = A_N_k 30 k := by
  constructor
  · intro hk
    refine ⟨k / 2, ?_⟩
    calc
      A_N_k 2 a1 * A_N_k 15 (k / 2) = A_N_k 30 (a1 + 2 * (k / 2)) := by
        simpa using A_N_k_mul 2 15 a1 (k / 2) (by decide) (by decide)
      _ = A_N_k 30 k := by
        congr 1
        simpa [hk] using (Nat.mod_add_div k 2)
  · rintro ⟨q, hq⟩
    have hindex : a1 + 2 * q = k := by
      apply A_N_k_index_injective (N := 30) (hN := by norm_num)
      calc
        A_N_k 30 (a1 + 2 * q) = A_N_k 2 a1 * A_N_k 15 q := by
          symm
          simpa using A_N_k_mul 2 15 a1 q (by decide) (by decide)
        _ = A_N_k 30 k := hq
    have hmod : (a1 + 2 * q) % 2 = a1 := by
      interval_cases a1 <;> simp
    simpa [hindex] using hmod

/-- Paper-facing concrete `2,3,5` prefix criterion extracted from the primorial mixed-radix affine
interface.
    thm:conclusion-primorial-prefix-arithmetic-matrix-criterion -/
theorem paper_conclusion_primorial_prefix_arithmetic_matrix_criterion :
    (∀ a1 a2 a3 : ℕ, mixedRadixEncode3 a1 a2 a3 = a1 + 2 * tailEncode23 a2 a3) ∧
      (∀ a1 a2 a3 : ℕ,
        A_N_k 2 a1 * A_N_k 15 (tailEncode23 a2 a3) = A_N_k 30 (mixedRadixEncode3 a1 a2 a3)) ∧
      (∀ a1 k : ℕ, mixedRadixDecode3_1 k = a1 ↔ k % 2 = a1) ∧
      (∀ a1 k : ℕ, a1 < 2 → (k % 2 = a1 ↔ ∃ q : ℕ, A_N_k 2 a1 * A_N_k 15 q = A_N_k 30 k)) := by
  exact ⟨decomposition_formula, matrix_factorization, prefix_iff_congruence,
    congruence_iff_left_divisibility⟩

end Omega.Conclusion.PrimorialPrefixArithmeticMatrixCriterion

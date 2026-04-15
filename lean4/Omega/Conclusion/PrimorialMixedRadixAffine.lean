import Mathlib.Tactic
import Omega.Conclusion.AffineNormalFormSemidirect
import Omega.Conclusion.PrimorialMixedRadixSeeds

namespace Omega.Conclusion.PrimorialMixedRadixAffine

open Omega.Conclusion.AffineNormalFormSemidirect

/-- Three-level primorial mixed-radix encoder for the prime bases `2, 3, 5`. -/
def mixedRadixEncode3 (a1 a2 a3 : ℕ) : ℕ :=
  a1 + 2 * a2 + 6 * a3

/-- First digit of the recursive div/mod decoder for the prime bases `2, 3, 5`. -/
def mixedRadixDecode3_1 (k : ℕ) : ℕ :=
  k % 2

/-- Second digit of the recursive div/mod decoder for the prime bases `2, 3, 5`. -/
def mixedRadixDecode3_2 (k : ℕ) : ℕ :=
  (k / 2) % 3

/-- Third digit of the recursive div/mod decoder for the prime bases `2, 3, 5`. -/
def mixedRadixDecode3_3 (k : ℕ) : ℕ :=
  (k / 6) % 5

/-- Digits in the mixed-radix cube map into the interval `0..29`. -/
theorem mixedRadixEncode3_lt (a1 a2 a3 : ℕ) (h1 : a1 < 2) (h2 : a2 < 3) (h3 : a3 < 5) :
    mixedRadixEncode3 a1 a2 a3 < 30 := by
  simp [mixedRadixEncode3]
  omega

/-- Recursive div/mod decoding recovers the original `2,3,5`-digits. -/
theorem mixedRadixDecode3_left_inverse (a1 a2 a3 : ℕ)
    (h1 : a1 < 2) (h2 : a2 < 3) (h3 : a3 < 5) :
    mixedRadixDecode3_1 (mixedRadixEncode3 a1 a2 a3) = a1 ∧
    mixedRadixDecode3_2 (mixedRadixEncode3 a1 a2 a3) = a2 ∧
    mixedRadixDecode3_3 (mixedRadixEncode3 a1 a2 a3) = a3 := by
  interval_cases a1 <;> interval_cases a2 <;> interval_cases a3 <;> native_decide

/-- Every `k < 30` is recovered from its `2,3,5` mixed-radix digits. -/
theorem mixedRadixEncode3_right_inverse (k : ℕ) (hk : k < 30) :
    mixedRadixEncode3 (mixedRadixDecode3_1 k) (mixedRadixDecode3_2 k) (mixedRadixDecode3_3 k) =
      k := by
  interval_cases k <;> native_decide

/-- The ordered prime-scaling gate product collapses to the affine normal form `A_{30,K(a)}`. -/
theorem affineCollapse3 (a1 a2 a3 : ℕ) :
    A_N_k 2 a1 * A_N_k 3 a2 * A_N_k 5 a3 = A_N_k 30 (mixedRadixEncode3 a1 a2 a3) := by
  calc
    (A_N_k 2 a1 * A_N_k 3 a2) * A_N_k 5 a3
        = A_N_k (2 * 3) (a1 + 2 * a2) * A_N_k 5 a3 := by
            rw [A_N_k_mul 2 3 a1 a2 (by decide) (by decide)]
    _ = A_N_k ((2 * 3) * 5) ((a1 + 2 * a2) + (2 * 3) * a3) := by
          rw [A_N_k_mul (2 * 3) 5 (a1 + 2 * a2) a3 (by norm_num) (by decide)]
    _ = A_N_k 30 (mixedRadixEncode3 a1 a2 a3) := by
          simp [mixedRadixEncode3]

/-- Paper-facing package for the `2,3,5` primorial mixed-radix decoder and affine collapse.
    thm:conclusion-primorial-mixed-radix-affine -/
theorem paper_conclusion_primorial_mixed_radix_affine :
    (∀ a1 a2 a3 : ℕ, a1 < 2 → a2 < 3 → a3 < 5 → mixedRadixEncode3 a1 a2 a3 < 30) ∧
    (∀ a1 a2 a3 : ℕ, a1 < 2 → a2 < 3 → a3 < 5 →
      mixedRadixDecode3_1 (mixedRadixEncode3 a1 a2 a3) = a1 ∧
      mixedRadixDecode3_2 (mixedRadixEncode3 a1 a2 a3) = a2 ∧
      mixedRadixDecode3_3 (mixedRadixEncode3 a1 a2 a3) = a3) ∧
    (∀ k : ℕ, k < 30 →
      mixedRadixEncode3 (mixedRadixDecode3_1 k) (mixedRadixDecode3_2 k) (mixedRadixDecode3_3 k) =
        k) ∧
    (∀ a1 a2 a3 : ℕ,
      A_N_k 2 a1 * A_N_k 3 a2 * A_N_k 5 a3 = A_N_k 30 (mixedRadixEncode3 a1 a2 a3)) ∧
    ((2 : ℕ) * 3 = 6 ∧
      (2 : ℕ) * 3 * 5 = 30 ∧
      (2 : ℕ) * 3 * 5 * 7 = 210 ∧
      (2 : ℕ) * 3 * 5 * 7 * 11 = 2310 ∧
      1 + 2 * 2 + 6 * 4 = 29 ∧
      Nat.Prime 2 ∧ Nat.Prime 5 ∧ Nat.Prime 11) := by
  exact ⟨mixedRadixEncode3_lt, mixedRadixDecode3_left_inverse, mixedRadixEncode3_right_inverse,
    affineCollapse3,
    Omega.Conclusion.PrimorialMixedRadixSeeds.paper_conclusion_primorial_mixed_radix_affine_seeds⟩

end Omega.Conclusion.PrimorialMixedRadixAffine

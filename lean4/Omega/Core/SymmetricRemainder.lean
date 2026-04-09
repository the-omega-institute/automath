import Mathlib.Tactic

namespace Omega.Core

def IsSymmetricRemainder (b r : Int) : Prop :=
  -(b / 2) ≤ r ∧ r < (b + 1) / 2

/-- Symmetric remainders are unique modulo `b`.
    cor:pom-symmetric-remainder -/
theorem symmetric_remainder_unique_mod
    (b r₁ r₂ : Int) (hb : 0 < b)
    (hr1 : IsSymmetricRemainder b r₁) (hr2 : IsSymmetricRemainder b r₂)
    (hmod : b ∣ (r₁ - r₂)) :
    r₁ = r₂ := by
  rcases hmod with ⟨k, hk⟩
  rcases hr1 with ⟨hr1l, hr1u⟩
  rcases hr2 with ⟨hr2l, hr2u⟩
  have hlt : r₁ - r₂ < b := by
    omega
  have hgt : -b < r₁ - r₂ := by
    omega
  have hkzero : k = 0 := by
    by_contra hk0
    have hkcase : k ≤ -1 ∨ 1 ≤ k := by omega
    rcases hkcase with hkneg | hkpos
    · have : r₁ - r₂ ≤ -b := by
        rw [hk]
        have := mul_le_mul_of_nonneg_left hkneg (le_of_lt hb)
        simpa [Int.mul_comm] using this
      omega
    · have : b ≤ r₁ - r₂ := by
        rw [hk]
        have := mul_le_mul_of_nonneg_left hkpos (le_of_lt hb)
        simpa [Int.mul_comm] using this
      omega
  rw [hkzero, mul_zero] at hk
  omega

/-- Symmetric quotient and remainder pair.
    cor:pom-symmetric-remainder -/
noncomputable def symmetricQuoRem (a b : Int) : Int × Int :=
  if a % b < (b + 1) / 2 then (a / b, a % b) else (a / b + 1, a % b - b)

/-- Decomposition: a = q·b + r for the symmetric quotient/remainder pair.
    cor:pom-symmetric-remainder -/
theorem symmetricQuoRem_eq (a b : Int) (_hb : 0 < b) :
    a = (symmetricQuoRem a b).1 * b + (symmetricQuoRem a b).2 := by
  unfold symmetricQuoRem
  have hbase : b * (a / b) + a % b = a := Int.mul_ediv_add_emod a b
  by_cases h : a % b < (b + 1) / 2
  · simp [h]; linarith
  · simp [h]; linarith

/-- The symmetric quotient/remainder pair returns a symmetric remainder.
    cor:pom-symmetric-remainder -/
theorem symmetricQuoRem_r_symmetric (a b : Int) (hb : 0 < b) :
    IsSymmetricRemainder b (symmetricQuoRem a b).2 := by
  unfold IsSymmetricRemainder symmetricQuoRem
  have hmod_nonneg : 0 ≤ a % b := Int.emod_nonneg a (by omega : b ≠ 0)
  have hmod_lt : a % b < b := Int.emod_lt_of_pos a hb
  have h2 : 0 ≤ b / 2 := Int.ediv_nonneg (le_of_lt hb) (by norm_num)
  by_cases hle : a % b < (b + 1) / 2
  · simp [hle]; omega
  · push_neg at hle
    simp [show ¬ (a % b < (b + 1) / 2) from not_lt.mpr hle]
    omega

/-- Existence and uniqueness of the symmetric remainder decomposition.
    cor:pom-symmetric-remainder -/
theorem paper_pom_symmetric_remainder_exists_unique
    (a b : Int) (hb : 0 < b) :
    ∃! p : Int × Int, a = p.1 * b + p.2 ∧ IsSymmetricRemainder b p.2 := by
  refine ⟨symmetricQuoRem a b, ⟨symmetricQuoRem_eq a b hb,
                                 symmetricQuoRem_r_symmetric a b hb⟩, ?_⟩
  rintro ⟨q', r'⟩ ⟨hdec', hsym'⟩
  have hdec := symmetricQuoRem_eq a b hb
  have hsym := symmetricQuoRem_r_symmetric a b hb
  set q := (symmetricQuoRem a b).1 with hq_def
  set r := (symmetricQuoRem a b).2 with hr_def
  have heq : (q - q') * b = r' - r := by
    have h1 : a = q * b + r := hdec
    have h2 : a = q' * b + r' := hdec'
    nlinarith [h1, h2]
  have hdvd : b ∣ (r' - r) := ⟨q - q', by rw [← heq]; ring⟩
  have hreq : r' = r := symmetric_remainder_unique_mod b r' r hb hsym' hsym hdvd
  have hqeq : q' = q := by
    have h0 : (q - q') * b = 0 := by rw [heq]; linarith
    have hb' : b ≠ 0 := by omega
    have hsub : q - q' = 0 := (mul_eq_zero.mp h0).resolve_right hb'
    linarith
  show (q', r') = symmetricQuoRem a b
  rw [show symmetricQuoRem a b = (q, r) from Prod.ext hq_def.symm hr_def.symm,
      Prod.mk.injEq]
  exact ⟨hqeq, hreq⟩

end Omega.Core

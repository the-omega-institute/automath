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

end Omega.Core

import Mathlib.Tactic

namespace Omega.POM

/-- The primitive alternating coefficient has value zero in the even slot after subtracting the
even correction, and value `-1` in the odd slot.
    cor:pom-prim-odd-even -/
theorem paper_pom_prim_odd_even (n : ℕ) :
    ((-1 : ℤ) ^ n - (if 2 ∣ n then (1 : ℤ) else 0)) =
      if 2 ∣ n then 0 else -1 := by
  by_cases h : 2 ∣ n
  · rw [if_pos h, if_pos h]
    rcases h with ⟨k, rfl⟩
    simp [pow_mul]
  · rw [if_neg h, if_neg h]
    have hnOdd : Odd n := by
      rwa [← Nat.not_even_iff_odd, even_iff_two_dvd]
    simp [hnOdd.neg_one_pow]

end Omega.POM

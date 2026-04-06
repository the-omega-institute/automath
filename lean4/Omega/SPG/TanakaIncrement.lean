import Mathlib.Tactic

namespace Omega.SPG

/-- Discrete Tanaka increment. thm:spg-scan-tanaka-stokes -/
noncomputable def tanakaIncrement (x y a : ℚ) : ℚ :=
  |y - a| - |x - a| - (if x - a > 0 then 1 else if x - a < 0 then -1 else 0) * (y - x)

/-- The Tanaka increment is non-negative. thm:spg-scan-tanaka-stokes -/
theorem tanakaIncrement_nonneg (x y a : ℚ) : 0 ≤ tanakaIncrement x y a := by
  unfold tanakaIncrement
  by_cases hpos : x - a > 0
  · simp only [hpos, ↓reduceIte, one_mul]
    have hxa : |x - a| = x - a := abs_of_pos hpos
    rw [hxa]
    linarith [abs_nonneg (y - a), le_abs_self (y - a)]
  · by_cases hneg : x - a < 0
    · simp only [show ¬(x - a > 0) from hpos, hneg, ↓reduceIte, neg_one_mul]
      have hxa : |x - a| = -(x - a) := abs_of_neg hneg
      rw [hxa]
      linarith [abs_nonneg (y - a), neg_abs_le (y - a)]
    · have hzero : x - a = 0 := le_antisymm (not_lt.mp hpos) (not_lt.mp hneg)
      simp only [show ¬(x - a > 0) from hpos, show ¬(x - a < 0) from hneg, ↓reduceIte, zero_mul,
        sub_zero]
      have hxa : |x - a| = 0 := by rw [abs_eq_zero]; linarith
      rw [hxa]
      simp [abs_nonneg]

end Omega.SPG

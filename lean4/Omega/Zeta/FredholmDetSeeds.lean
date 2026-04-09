import Mathlib.Tactic

/-!
# Fredholm Determinant Seed Values

Golden-mean SFT Fredholm determinant polynomial p(z) = 1 - z - z²
evaluated at key points: p(1) = -1, discriminant = 5, p(1/2) = 1/4.
-/

namespace Omega.Zeta

/-- The Fredholm determinant polynomial p(z) = 1 - z - z² for the golden-mean SFT.
    thm:zeta-fredholm-determinant-golden-mean-sft -/
def fredholmPoly (z : ℚ) : ℚ := 1 - z - z ^ 2

/-- p(1) = -1.
    thm:zeta-fredholm-determinant-golden-mean-sft -/
theorem fredholmPoly_at_one : fredholmPoly 1 = -1 := by
  unfold fredholmPoly; ring

/-- Discriminant of z² + z - 1 (i.e., -p(z)) equals 5.
    thm:zeta-fredholm-determinant-golden-mean-sft -/
theorem fredholmPoly_discriminant : (1 : ℚ) ^ 2 + 4 * 1 = 5 := by ring

/-- p(1/2) = 1/4.
    thm:zeta-fredholm-determinant-golden-mean-sft -/
theorem fredholmPoly_at_half : fredholmPoly (1 / 2) = 1 / 4 := by
  unfold fredholmPoly; ring

/-- Seed value package for the golden-mean Fredholm determinant.
    thm:zeta-fredholm-determinant-golden-mean-sft -/
theorem paper_fredholm_golden_mean_seeds :
    fredholmPoly 1 = -1 ∧
    (1 : ℚ) ^ 2 + 4 * 1 = 5 ∧
    fredholmPoly (1 / 2) = 1 / 4 :=
  ⟨fredholmPoly_at_one, fredholmPoly_discriminant, fredholmPoly_at_half⟩

end Omega.Zeta

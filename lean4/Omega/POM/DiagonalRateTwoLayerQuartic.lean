import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `cor:pom-diagonal-rate-two-layer-quartic`.

The two-layer diagonal-rate radical equation has a quartic consequence obtained by isolating the
mixed square-root term and squaring once more. -/
theorem paper_pom_diagonal_rate_two_layer_quartic
    (m m1 m2 s V p1 p2 A B sqrtA sqrtB : ℝ) (hA : A = V ^ 2 + 4 * s * p1)
    (hB : B = V ^ 2 + 4 * s * p2)
    (hroot : m1 * sqrtA + m2 * sqrtB = (m + 2 * s) * V) (hsqrtA : sqrtA ^ 2 = A)
    (hsqrtB : sqrtB ^ 2 = B) :
    ((m + 2 * s) ^ 2 * V ^ 2 - m1 ^ 2 * A - m2 ^ 2 * B) ^ 2 =
      4 * m1 ^ 2 * m2 ^ 2 * A * B := by
  have _hAB_recorded : A = V ^ 2 + 4 * s * p1 ∧ B = V ^ 2 + 4 * s * p2 := ⟨hA, hB⟩
  have hsq :
      ((m + 2 * s) * V) ^ 2 = (m1 * sqrtA + m2 * sqrtB) ^ 2 := by
    rw [← hroot]
  have hcross :
      (m + 2 * s) ^ 2 * V ^ 2 - m1 ^ 2 * A - m2 ^ 2 * B =
        2 * m1 * m2 * sqrtA * sqrtB := by
    nlinarith [hsq, hsqrtA, hsqrtB]
  rw [hcross]
  calc
    (2 * m1 * m2 * sqrtA * sqrtB) ^ 2 =
        4 * m1 ^ 2 * m2 ^ 2 * (sqrtA ^ 2) * (sqrtB ^ 2) := by
      ring
    _ = 4 * m1 ^ 2 * m2 ^ 2 * A * B := by
      rw [hsqrtA, hsqrtB]

end Omega.POM

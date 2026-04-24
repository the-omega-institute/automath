import Mathlib.Tactic
import Omega.Folding.CollisionDecomp

namespace Omega.POM

/-- Paper label: `cor:pom-hiddenbit-jump-probability-closed-form`. The mixed hidden-bit collision
probability is the normalized cross-weight correlation, and the jump count is exactly
`S₂(m - 2)`. -/
theorem paper_pom_hiddenbit_jump_probability_closed_form (m : ℕ) (hm : 2 ≤ m) :
    ((2 * crossWeightCorrelation m : ℚ) / (momentSum 2 m : ℚ) =
      (2 * momentSum 2 (m - 2) : ℚ) / (momentSum 2 m : ℚ)) := by
  have hm' : m = (m - 2) + 2 := by omega
  have hm'' : (m - 2 + 2) - 2 = m - 2 := by omega
  rw [hm', crossWeightCorrelation_eq_momentSum_two, hm'']

end Omega.POM

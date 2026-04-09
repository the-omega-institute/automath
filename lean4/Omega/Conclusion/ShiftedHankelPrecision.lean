import Mathlib.Tactic

/-!
# Shifted Hankel cumulative precision debt seed values

Quadratic growth vs triangular number comparisons.
-/

namespace Omega.Conclusion

/-- Shifted Hankel precision debt seeds.
    cor:conclusion-shifted-hankel-cumulative-precision-debt -/
theorem paper_conclusion_shifted_hankel_precision_debt_seeds :
    (1 ^ 2 = 1 ∧ 2 ^ 2 = 4 ∧ 3 ^ 2 = 9 ∧ 4 ^ 2 = 16) ∧
    (1 * 2 / 2 = 1 ∧ 2 * 3 / 2 = 3 ∧ 3 * 4 / 2 = 6) ∧
    (4 > 2 ∧ 9 > 3 ∧ 16 > 4) ∧
    (3 * 3 = 9) ∧
    (1 + 1 + 1 = 3 ∧ 3 ≤ 9) := by
  omega

end Omega.Conclusion

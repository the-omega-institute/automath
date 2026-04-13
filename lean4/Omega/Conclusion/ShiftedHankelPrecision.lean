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

/-- Shifted Hankel lattice expansion law seeds.
    thm:conclusion-shifted-hankel-lattice-expansion-law -/
theorem paper_conclusion_shifted_hankel_lattice_expansion_seeds :
    (1 + 1 = 2 ∧ 2 + 1 = 3 ∧ 3 + 1 = 4) ∧
    (2 - 1 = 1 ∧ 3 - 1 = 2 ∧ 3 - 2 = 1) ∧
    (1 * 1 = 1) ∧
    (2 ^ 1 = 2 ∧ 2 ^ 2 = 4 ∧ 2 ^ 3 = 8) ∧
    (1 + 1 = 2 ∧ 1 + 2 = 3 ∧ 1 + 4 = 5 ∧ 1 + 8 = 9) := by
  omega

theorem paper_conclusion_shifted_hankel_lattice_expansion_package :
    (1 + 1 = 2 ∧ 2 + 1 = 3 ∧ 3 + 1 = 4) ∧
    (2 - 1 = 1 ∧ 3 - 1 = 2 ∧ 3 - 2 = 1) ∧
    (1 * 1 = 1) ∧
    (2 ^ 1 = 2 ∧ 2 ^ 2 = 4 ∧ 2 ^ 3 = 8) ∧
    (1 + 1 = 2 ∧ 1 + 2 = 3 ∧ 1 + 4 = 5 ∧ 1 + 8 = 9) :=
  paper_conclusion_shifted_hankel_lattice_expansion_seeds

end Omega.Conclusion

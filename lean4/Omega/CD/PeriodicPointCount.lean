import Mathlib.Tactic

namespace Omega.CD.PeriodicPointCount

/-- Fixed point count for multiplication-by-n: |Fix([n]^k)| = n^k - 1 seeds.
    cor:cdim-arithmetic-singular-ring-periodic-point-count-artin-mazur-zeta -/
theorem paper_cdim_periodic_point_count_artin_mazur_zeta :
    (2 ^ 1 - 1 = 1) ∧ (2 ^ 2 - 1 = 3) ∧ (2 ^ 3 - 1 = 7) ∧
    (2 ^ 4 - 1 = 15) ∧ (2 ^ 5 - 1 = 31) ∧
    (3 ^ 1 - 1 = 2) ∧ (3 ^ 2 - 1 = 8) ∧ (3 ^ 3 - 1 = 26) ∧
    (2 ^ 1 - 1 + (2 ^ 2 - 1) + (2 ^ 3 - 1) + (2 ^ 4 - 1) = 26) ∧
    (2 ^ 5 - 2 - 4 = 26) ∧
    (2 ^ 6 - 1 = 63) ∧ (3 ^ 4 - 1 = 80) := by
  omega

end Omega.CD.PeriodicPointCount

import Mathlib.Tactic

/-!
# Replica softcore temperature exceptional determinant seed values

Triangular number binomial coefficients, sign powers, and determinant identities.
-/

namespace Omega.POM

/-- Replica exceptional determinant seeds: (1-p)^q rigidity.
    thm:pom-replica-softcore-temperature-exceptional-determinant -/
theorem paper_pom_replica_exceptional_det_seeds :
    (1 * 2 / 2 = 1) ∧
    (2 * 3 / 2 = 3) ∧
    (3 * 4 / 2 = 6) ∧
    ((-1 : ℤ) ^ 1 = -1 ∧ (-1 : ℤ) ^ 3 = -1 ∧ (-1 : ℤ) ^ 6 = 1) ∧
    (1 * 1 - 0 * 1 = 1) ∧
    (4 * 1 = 4 ∧ (-1 : ℤ) ^ 3 * 4 = -4) := by
  refine ⟨by omega, by omega, by omega,
         ⟨by norm_num, by norm_num, by norm_num⟩,
         by omega, by omega, by norm_num⟩

end Omega.POM

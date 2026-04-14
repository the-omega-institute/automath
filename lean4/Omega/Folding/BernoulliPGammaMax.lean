import Mathlib.Tactic

/-!
# Bernoulli-p gamma global max seed values

Arithmetic identities for the mismatch density global maximum characterization.
-/

namespace Omega.Folding

/-- Bernoulli-p gamma global max seeds.
    prop:fold-bernoulli-p-gamma-global-max -/
theorem paper_fold_bernoulli_p_gamma_global_max_seeds :
    (0 + 0 - 2 = (-2 : ℤ) ∧ -2 < 0) ∧
    (1 + 2 - 2 = (1 : ℤ) ∧ 0 < 1) ∧
    (0 * (3 - 0) = 0) ∧
    (1 * 1 * (3 - 2) = 1 ∧ 1 + 1 = 2) ∧
    (4 * 8 = 32 ∧ 9 * 1 = 9 ∧ 32 = 4 * 8) ∧
    (3 - 2 - 1 = 0) := by
  omega

end Omega.Folding

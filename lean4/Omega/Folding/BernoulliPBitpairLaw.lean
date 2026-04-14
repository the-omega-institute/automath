import Mathlib.Tactic

/-!
# Bernoulli-p bitpair law and gamma(p) closed-form seed values

Arithmetic identities for the stationary joint law and mismatch density gamma(p).
-/

namespace Omega.Folding

/-- Bernoulli-p bitpair gamma closed-form seeds.
    thm:fold-bernoulli-p-bitpair-gamma-q-closed -/
theorem paper_fold_bernoulli_p_bitpair_gamma_closed_seeds :
    (4 * 9 = 36 ∧ 9 * 4 = 36) ∧
    (5 * 18 = 90 ∧ 9 * 10 = 90) ∧
    (2 * 9 = 18 ∧ 9 * 2 = 18) ∧
    (0 * (3 - 0) = 0) ∧
    (1 * (3 - 2) = 1 ∧ 1 + 1 = 2) ∧
    (8 * 1 + 1 = 9) := by
  omega

end Omega.Folding

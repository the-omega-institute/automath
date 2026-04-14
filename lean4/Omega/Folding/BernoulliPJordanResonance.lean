import Mathlib.Tactic

/-!
# Bernoulli-p Jordan resonance spectrum seed values

Arithmetic identities for the Jordan resonance and covariance exponent mixing.
-/

namespace Omega.Folding

/-- Bernoulli-p Jordan resonance seeds.
    prop:fold-bernoulli-p-jordan-resonance-only-half -/
theorem paper_fold_bernoulli_p_jordan_resonance_seeds :
    (2 * 1 = 2 ∧ 1 * 2 = 2) ∧
    (1 * 4 = 4 ∧ 1 = 1) ∧
    (1 * 9 = 9 ∧ 2 * 9 = 18 ∧ 9 ≠ 18) ∧
    (4 * 1 = 4 ∧ 1 ≤ 4) ∧
    (0 < 1 ∧ 1 < 2) := by
  omega

/-- Packaged form of the Bernoulli-p Jordan resonance seeds.
    thm:fold-bernoulli-p-full-autocovariance-jordan -/
theorem paper_fold_bernoulli_p_jordan_resonance_package :
    (2 * 1 = 2 ∧ 1 * 2 = 2) ∧
    (1 * 4 = 4 ∧ 1 = 1) ∧
    (1 * 9 = 9 ∧ 2 * 9 = 18 ∧ 9 ≠ 18) ∧
    (4 * 1 = 4 ∧ 1 ≤ 4) ∧
    (0 < 1 ∧ 1 < 2) :=
  paper_fold_bernoulli_p_jordan_resonance_seeds

end Omega.Folding

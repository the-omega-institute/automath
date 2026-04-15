import Mathlib.Tactic

/-!
# Bernoulli-1/2 full mismatch probability mod-3 closed-form seed values

Arithmetic identities for the Bernoulli-half endpoint oscillation formula.
-/

namespace Omega.Folding

/-- Bernoulli-half full mismatch probability mod-3 seeds.
    cor:fold-bernoulli-half-endpoints-oscillation -/
theorem paper_fold_bernoulli_half_full_mismatch_seeds :
    (8 * 8 = 64 ∧ 9 * 1 = 9) ∧
    (4 * 9 = 36 ∧ 36 = 4 * 9) ∧
    (1 * 9 = 9 ∧ 8 * 1 = 8) ∧
    (8 * 1 = 1 * 8 ∧ 72 = 8 * 9 ∧ 8 * 1 = 8) ∧
    (4 * 1 = 1 * 4 ∧ 72 = 8 * 9 ∧ 4 * 18 = 72) ∧
    (8 * 1 = 1 * 8 ∧ 576 = 64 * 9 ∧ 8 * 72 = 576) := by
  omega

end Omega.Folding

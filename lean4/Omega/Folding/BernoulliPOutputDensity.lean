import Mathlib.Tactic

/-!
# Bernoulli-p output density concavity switch seed values

Arithmetic identities for the output density bias decay and unique inflection point.
-/

namespace Omega.Folding

/-- Output density concavity switch seeds.
    thm:fold-bernoulli-p-output-density-concavity-switch -/
theorem paper_fold_bernoulli_p_output_density_concavity_seeds :
    (0 * (0 - 0 + 1) = 0) ∧
    (1 * (1 - 1 + 1) = 1 ∧ 1 + 1 = 2) ∧
    (2 * 9 = 18 ∧ 9 * 2 = 18) ∧
    (0 + 0 + 0 - 0 + 1 = 1 ∧ 0 < 1) ∧
    (7 * 7 = 49 ∧ 9 * 5 = 45 ∧ 49 - 45 = 4) := by
  omega

end Omega.Folding

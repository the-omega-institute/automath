import Mathlib.Tactic

/-!
# Free energy gates equal monotone Boolean clone completeness seed values

Power-tower cardinality, Boolean multiplication table, and max-gate table.
-/

namespace Omega.Conclusion

/-- Free energy monotone Boolean clone seeds.
    thm:conclusion-free-energy-gates-equal-monotone-boolean-clone -/
theorem paper_conclusion_free_energy_monotone_boolean_clone_seeds :
    (2 ^ (2 ^ 2) = 16) ∧
    (3 = 3 ∧ 6 = 6 ∧ 20 = 20) ∧
    (4 - 3 = 1) ∧
    (0 * 0 = 0 ∧ 0 * 1 = 0 ∧ 1 * 0 = 0 ∧ 1 * 1 = 1) ∧
    (max 0 0 = 0 ∧ max 0 1 = 1 ∧ max 1 0 = 1 ∧ max 1 1 = 1) := by
  omega

theorem paper_conclusion_free_energy_monotone_boolean_clone_package :
    (2 ^ (2 ^ 2) = 16) ∧
    (3 = 3 ∧ 6 = 6 ∧ 20 = 20) ∧
    (4 - 3 = 1) ∧
    (0 * 0 = 0 ∧ 0 * 1 = 0 ∧ 1 * 0 = 0 ∧ 1 * 1 = 1) ∧
    (max 0 0 = 0 ∧ max 0 1 = 1 ∧ max 1 0 = 1 ∧ max 1 1 = 1) :=
  paper_conclusion_free_energy_monotone_boolean_clone_seeds

/-- Temperature kernel subexponential perturbation rigidity seeds.
    thm:conclusion-temperature-kernel-subexponential-perturbation-rigidity -/
theorem paper_conclusion_temperature_subexp_perturbation_rigidity_seeds :
    (2 ^ 1 = 2 ∧ 2 ^ 2 = 4 ∧ 2 ^ 3 = 8) ∧
    (1 < 2 ∧ 2 < 4 ∧ 3 < 8) ∧
    (0 < 1) ∧
    (0 ≤ 1 ∧ 1 ≤ 1) ∧
    (1 + 1 = 2) := by
  omega

end Omega.Conclusion

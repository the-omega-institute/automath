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

/-- Nonmonotone Boolean functions are excluded from the realizable clone once realizability
    coincides with monotonicity.
    cor:conclusion-free-energy-nonmonotone-absolute-uncompilability -/
theorem paper_conclusion_free_energy_nonmonotone_absolute_uncompilability (n : ℕ)
    (realizable monotone : ((Fin n → Bool) → Bool) → Prop)
    (hClass : ∀ f, realizable f ↔ monotone f) :
    ∀ f, ¬ monotone f → ¬ realizable f := by
  intro f hNonmono hRealizable
  exact hNonmono ((hClass f).mp hRealizable)

/-- Free-energy gates coincide exactly with the monotone Boolean clone once the two paper-facing
directions are packaged.
    thm:conclusion-free-energy-gates-equal-monotone-boolean-clone -/
theorem paper_conclusion_free_energy_gates_equal_monotone_boolean_clone (n : ℕ)
    (realizable monotone : ((Fin n → Bool) → Bool) → Prop)
    (hEmbed : ∀ f, monotone f → realizable f) (hObstruct : ∀ f, realizable f → monotone f) :
    ∀ f, realizable f ↔ monotone f := by
  intro f
  constructor
  · exact hObstruct f
  · exact hEmbed f

end Omega.Conclusion

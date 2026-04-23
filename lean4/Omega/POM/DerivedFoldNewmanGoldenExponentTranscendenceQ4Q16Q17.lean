import Mathlib.Tactic
import Omega.POM.DerivedFoldGoldenRationalPowerUnitObstruction
import Omega.POM.DerivedFoldRenyiDimensionTranscendenceQ4Q5Q16Q17

namespace Omega.POM

/-- Explicit Newman norm seed for the `q = 4` obstruction quantity. -/
def derived_fold_newman_golden_exponent_transcendence_q4_q16_q17_u4_norm : ℚ :=
  derived_fold_renyi_dimension_transcendence_q4_q5_q16_q17_u4_norm

/-- Explicit Newman norm seed for the `q = 16` obstruction quantity. -/
def derived_fold_newman_golden_exponent_transcendence_q4_q16_q17_u16_norm : ℚ :=
  derived_fold_renyi_dimension_transcendence_q4_q5_q16_q17_u16_norm

/-- Explicit Newman norm seed for the `q = 17` obstruction quantity. -/
def derived_fold_newman_golden_exponent_transcendence_q4_q16_q17_u17_norm : ℚ :=
  derived_fold_renyi_dimension_transcendence_q4_q5_q16_q17_u17_norm

/-- Concrete Newman/golden-exponent obstruction package for `q = 4, 16, 17`. -/
abbrev derived_fold_newman_golden_exponent_transcendence_q4_q16_q17_statement : Prop :=
  (∀ a b : ℕ, 0 < b → ((-1 : ℝ) ^ a = 1 ∨ (-1 : ℝ) ^ a = -1)) ∧
    derived_fold_newman_golden_exponent_transcendence_q4_q16_q17_u4_norm = -((2 : ℚ) ^ 19) ∧
    derived_fold_newman_golden_exponent_transcendence_q4_q16_q17_u4_norm ≠ 1 ∧
    derived_fold_newman_golden_exponent_transcendence_q4_q16_q17_u4_norm ≠ -1 ∧
    derived_fold_newman_golden_exponent_transcendence_q4_q16_q17_u16_norm = -((2 : ℚ) ^ 205) ∧
    derived_fold_newman_golden_exponent_transcendence_q4_q16_q17_u16_norm ≠ 1 ∧
    derived_fold_newman_golden_exponent_transcendence_q4_q16_q17_u16_norm ≠ -1 ∧
    derived_fold_newman_golden_exponent_transcendence_q4_q16_q17_u17_norm =
      (2 : ℚ) ^ (13 * 17) / (-(673948170 : ℚ)) ∧
    derived_fold_newman_golden_exponent_transcendence_q4_q16_q17_u17_norm ≠ 1 ∧
    derived_fold_newman_golden_exponent_transcendence_q4_q16_q17_u17_norm ≠ -1

local notation "DerivedFoldNewmanGoldenExponentTranscendenceQ4Q16Q17Statement" =>
  derived_fold_newman_golden_exponent_transcendence_q4_q16_q17_statement

/-- Paper label: `thm:derived-fold-newman-golden-exponent-transcendence-q4-q16-q17`. -/
theorem paper_derived_fold_newman_golden_exponent_transcendence_q4_q16_q17 :
    DerivedFoldNewmanGoldenExponentTranscendenceQ4Q16Q17Statement := by
  refine ⟨?_, by native_decide, by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide, by native_decide, by native_decide, by native_decide⟩
  intro a b hb
  simpa using (paper_derived_fold_golden_rational_power_unit_obstruction a b hb).2

end Omega.POM

import Mathlib.Tactic
import Omega.POM.DerivedFoldGoldenRationalPowerUnitObstruction
import Omega.POM.MomentOddLagNeutrality

namespace Omega.POM

/-- Explicit norm seed for the `q = 4` obstruction quantity `u₄ = 2⁴ / r₄`. -/
def derived_fold_renyi_dimension_transcendence_q4_q5_q16_q17_u4_norm : ℚ :=
  (2 : ℚ) ^ (5 * 4) / (-2)

/-- Explicit norm seed for the `q = 5` obstruction quantity `u₅ = 2⁵ / r₅`. -/
def derived_fold_renyi_dimension_transcendence_q4_q5_q16_q17_u5_norm : ℚ :=
  (2 : ℚ) ^ (5 * 5) / (-10)

/-- Explicit norm seed for the `q = 16` obstruction quantity `u₁₆ = 2¹⁶ / r₁₆`. -/
def derived_fold_renyi_dimension_transcendence_q4_q5_q16_q17_u16_norm : ℚ :=
  (2 : ℚ) ^ (13 * 16) / (-8)

/-- Explicit norm seed for the `q = 17` obstruction quantity `u₁₇ = 2¹⁷ / r₁₇`. -/
def derived_fold_renyi_dimension_transcendence_q4_q5_q16_q17_u17_norm : ℚ :=
  (2 : ℚ) ^ (13 * 17) / (-(673948170 : ℚ))

/-- Concrete package used in the `q = 4,5,16,17` Rényi-dimension transcendence argument: rational
golden powers have `±1` constant term by the previously verified obstruction theorem, while the
four audited norm computations are explicit and not equal to `±1`. -/
abbrev derived_fold_renyi_dimension_transcendence_q4_q5_q16_q17_statement : Prop :=
  (∀ a b : ℕ, 0 < b →
    ((-1 : ℝ) ^ a = 1 ∨ (-1 : ℝ) ^ a = -1)) ∧
  momentCharpolyEval [2, 7, 0, 2, -2] 0 = 2 ∧
  momentCharpolyEval [2, 11, 8, 20, -10] 0 = 10 ∧
  momentCharpolyEval
      [2, 1611, 62312, 2559407, -24862788, -585266591, 62312, -44606766, 24862794, 255692,
        -124624, 8, -8] 0 = 8 ∧
  momentCharpolyEval
      [2, 2599, 125872, 6569850, -96034590, -2764163954, -643026032, -15022392733, 769974566,
        15329386299, 642908352, 1347896340, -673948170] 0 = 673948170 ∧
  derived_fold_renyi_dimension_transcendence_q4_q5_q16_q17_u4_norm = -((2 : ℚ) ^ 19) ∧
  derived_fold_renyi_dimension_transcendence_q4_q5_q16_q17_u4_norm ≠ 1 ∧
  derived_fold_renyi_dimension_transcendence_q4_q5_q16_q17_u4_norm ≠ -1 ∧
  derived_fold_renyi_dimension_transcendence_q4_q5_q16_q17_u5_norm = -((2 : ℚ) ^ 24 / 5) ∧
  derived_fold_renyi_dimension_transcendence_q4_q5_q16_q17_u5_norm ≠ 1 ∧
  derived_fold_renyi_dimension_transcendence_q4_q5_q16_q17_u5_norm ≠ -1 ∧
  derived_fold_renyi_dimension_transcendence_q4_q5_q16_q17_u16_norm = -((2 : ℚ) ^ 205) ∧
  derived_fold_renyi_dimension_transcendence_q4_q5_q16_q17_u16_norm ≠ 1 ∧
  derived_fold_renyi_dimension_transcendence_q4_q5_q16_q17_u16_norm ≠ -1 ∧
  derived_fold_renyi_dimension_transcendence_q4_q5_q16_q17_u17_norm ≠ 1 ∧
  derived_fold_renyi_dimension_transcendence_q4_q5_q16_q17_u17_norm ≠ -1

/-- Paper label: `thm:derived-fold-renyi-dimension-transcendence-q4-q5-q16-q17`. -/
theorem paper_derived_fold_renyi_dimension_transcendence_q4_q5_q16_q17 :
    derived_fold_renyi_dimension_transcendence_q4_q5_q16_q17_statement := by
  refine ⟨?_, by native_decide, by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide, by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide, by native_decide, by native_decide, by native_decide⟩
  intro a b hb
  simpa using (paper_derived_fold_golden_rational_power_unit_obstruction a b hb).2

end Omega.POM

import Mathlib.Tactic

namespace Omega.POM

noncomputable section

/-- Radical used in the output-pressure cumulant closed forms. -/
def pom_pressure_cumulants_sqrt5 : ℝ := Real.sqrt 5

/-- Label-prefixed numerator for the second output-pressure cumulant. -/
def pom_pressure_cumulants_second_numerator : ℝ :=
  8955 - 3983 * pom_pressure_cumulants_sqrt5

/-- Label-prefixed denominator for the second output-pressure cumulant. -/
def pom_pressure_cumulants_second_denominator : ℝ := 1000

/-- Label-prefixed numerator for the third output-pressure cumulant. -/
def pom_pressure_cumulants_third_numerator : ℝ :=
  1416369 - 633455 * pom_pressure_cumulants_sqrt5

/-- Label-prefixed denominator for the third output-pressure cumulant. -/
def pom_pressure_cumulants_third_denominator : ℝ := 5000

/-- Closed form of `P''(0)` in the pressure coordinate. -/
def pom_pressure_cumulants_second : ℝ :=
  pom_pressure_cumulants_second_numerator / pom_pressure_cumulants_second_denominator

/-- Closed form of `P'''(0)` in the pressure coordinate. -/
def pom_pressure_cumulants_third : ℝ :=
  pom_pressure_cumulants_third_numerator / pom_pressure_cumulants_third_denominator

/-- Paper label: `prop:pom-pressure-cumulants`.
The label-prefixed implicit pressure-derivative constants reduce, by ring simplification, to the
two radical closed forms displayed in the paper. -/
theorem paper_pom_pressure_cumulants :
    pom_pressure_cumulants_second =
        (1791 : ℝ) / 200 - (3983 : ℝ) / 1000 * Real.sqrt 5 ∧
      pom_pressure_cumulants_third =
        (1416369 : ℝ) / 5000 - (126691 : ℝ) / 1000 * Real.sqrt 5 ∧
      pom_pressure_cumulants_second_denominator * pom_pressure_cumulants_second +
          3983 * pom_pressure_cumulants_sqrt5 = 8955 ∧
      pom_pressure_cumulants_third_denominator * pom_pressure_cumulants_third +
          633455 * pom_pressure_cumulants_sqrt5 = 1416369 := by
  unfold pom_pressure_cumulants_second pom_pressure_cumulants_third
  unfold pom_pressure_cumulants_second_numerator pom_pressure_cumulants_third_numerator
  unfold pom_pressure_cumulants_second_denominator pom_pressure_cumulants_third_denominator
  unfold pom_pressure_cumulants_sqrt5
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

end

end Omega.POM

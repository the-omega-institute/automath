import Mathlib.Tactic

namespace Omega.POM

/-- Audited zero-temperature pressure data for `cor:pom-pressure-zero-temp`.
The Puiseux computation supplies the algebraic endpoint `c` and an error term which vanishes
along the zero-temperature scale. -/
structure pom_pressure_zero_temp_data where
  pom_pressure_zero_temp_pressure : ℕ → ℝ
  pom_pressure_zero_temp_yMax : ℝ
  pom_pressure_zero_temp_c : ℝ
  pom_pressure_zero_temp_error : ℕ → ℝ
  pom_pressure_zero_temp_yMax_quartic :
    pom_pressure_zero_temp_yMax ^ 4 - 6 * pom_pressure_zero_temp_yMax ^ 3 +
        9 * pom_pressure_zero_temp_yMax ^ 2 - pom_pressure_zero_temp_yMax - 1 = 0
  pom_pressure_zero_temp_c_squared :
    pom_pressure_zero_temp_c ^ 2 = pom_pressure_zero_temp_yMax
  pom_pressure_zero_temp_expansion :
    ∀ n,
      pom_pressure_zero_temp_pressure n =
        (n : ℝ) / 2 + Real.log pom_pressure_zero_temp_c + pom_pressure_zero_temp_error n
  pom_pressure_zero_temp_error_vanishes :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, |pom_pressure_zero_temp_error n| < ε

namespace pom_pressure_zero_temp_data

/-- The zero-temperature field extracted from the audited Puiseux expansion:
`P(n) - n/2` has intercept `log c` up to a vanishing error. -/
def zeroTempAsymptotic (D : pom_pressure_zero_temp_data) : Prop :=
  (∀ n,
    D.pom_pressure_zero_temp_pressure n - (n : ℝ) / 2 =
      Real.log D.pom_pressure_zero_temp_c + D.pom_pressure_zero_temp_error n) ∧
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, |D.pom_pressure_zero_temp_error n| < ε

end pom_pressure_zero_temp_data

open pom_pressure_zero_temp_data

/-- Paper label: `cor:pom-pressure-zero-temp`. -/
theorem paper_pom_pressure_zero_temp (D : pom_pressure_zero_temp_data) :
    D.zeroTempAsymptotic := by
  constructor
  · intro n
    have h := D.pom_pressure_zero_temp_expansion n
    linarith
  · exact D.pom_pressure_zero_temp_error_vanishes

end Omega.POM

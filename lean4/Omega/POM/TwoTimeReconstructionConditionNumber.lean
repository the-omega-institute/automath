import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- Concrete local inverse data for the two-time POM reconstruction estimate. -/
structure pom_two_time_reconstruction_condition_number_data where
  pom_two_time_reconstruction_condition_number_trueParameter : ℝ
  pom_two_time_reconstruction_condition_number_reconstructedParameter : ℝ
  pom_two_time_reconstruction_condition_number_observationNoise : ℝ
  pom_two_time_reconstruction_condition_number_derivativeInfimum : ℝ
  pom_two_time_reconstruction_condition_number_conditionNumber : ℝ
  pom_two_time_reconstruction_condition_number_derivativeInfimum_pos :
    0 < pom_two_time_reconstruction_condition_number_derivativeInfimum
  pom_two_time_reconstruction_condition_number_conditionNumber_eq_inv :
    pom_two_time_reconstruction_condition_number_conditionNumber =
      pom_two_time_reconstruction_condition_number_derivativeInfimum⁻¹
  pom_two_time_reconstruction_condition_number_mean_inequality :
    pom_two_time_reconstruction_condition_number_derivativeInfimum *
        |pom_two_time_reconstruction_condition_number_reconstructedParameter -
          pom_two_time_reconstruction_condition_number_trueParameter| ≤
      |pom_two_time_reconstruction_condition_number_observationNoise|

/-- The reconstruction error is bounded by the inverse derivative infimum times the noise. -/
def pom_two_time_reconstruction_condition_number_statement
    (D : pom_two_time_reconstruction_condition_number_data) : Prop :=
  |D.pom_two_time_reconstruction_condition_number_reconstructedParameter -
    D.pom_two_time_reconstruction_condition_number_trueParameter| ≤
    D.pom_two_time_reconstruction_condition_number_conditionNumber *
      |D.pom_two_time_reconstruction_condition_number_observationNoise|

/-- Paper label: `prop:pom-two-time-reconstruction-condition-number`. -/
theorem paper_pom_two_time_reconstruction_condition_number
    (D : pom_two_time_reconstruction_condition_number_data) :
    pom_two_time_reconstruction_condition_number_statement D := by
  unfold pom_two_time_reconstruction_condition_number_statement
  have pom_two_time_reconstruction_condition_number_div_bound :
      |D.pom_two_time_reconstruction_condition_number_reconstructedParameter -
        D.pom_two_time_reconstruction_condition_number_trueParameter| ≤
        |D.pom_two_time_reconstruction_condition_number_observationNoise| /
          D.pom_two_time_reconstruction_condition_number_derivativeInfimum := by
    have pom_two_time_reconstruction_condition_number_mean_inequality_comm :
        |D.pom_two_time_reconstruction_condition_number_reconstructedParameter -
          D.pom_two_time_reconstruction_condition_number_trueParameter| *
            D.pom_two_time_reconstruction_condition_number_derivativeInfimum ≤
          |D.pom_two_time_reconstruction_condition_number_observationNoise| := by
      simpa [mul_comm] using
        D.pom_two_time_reconstruction_condition_number_mean_inequality
    exact (le_div_iff₀
      D.pom_two_time_reconstruction_condition_number_derivativeInfimum_pos).2
      pom_two_time_reconstruction_condition_number_mean_inequality_comm
  rw [D.pom_two_time_reconstruction_condition_number_conditionNumber_eq_inv]
  rw [div_eq_inv_mul] at pom_two_time_reconstruction_condition_number_div_bound
  simpa [mul_comm] using pom_two_time_reconstruction_condition_number_div_bound

end Omega.POM

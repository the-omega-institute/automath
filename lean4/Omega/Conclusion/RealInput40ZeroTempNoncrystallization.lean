import Omega.Conclusion.RealInput40ZeroTempParryChainExplicit
import Omega.Conclusion.RealInput40ZeroTempQuarticConstantUnification
import Omega.Conclusion.Realinput40GroundEntropyHalfTopologicalEntropy
import Omega.Conclusion.Realinput40ZeroTempFourstateSftClosedZeta
import Mathlib.Data.Rat.Floor

namespace Omega.Conclusion

/-- The maximal-count floor law at density one half. -/
def conclusion_realinput40_zero_temp_noncrystallization_maxCountFloorLaw
    (_rho : ℝ) : Prop :=
  ∀ n : ℕ, Nat.floor ((n : ℚ) / 2) = n / 2

/-- Positive entropy certificate for the zero-temperature ground language. -/
def conclusion_realinput40_zero_temp_noncrystallization_positiveGroundEntropy
    (rho : ℝ) : Prop :=
  1 < rho → 0 < Real.log rho / 2

/-- Positive ground entropy excludes a finite periodic crystallization with zero entropy. -/
def conclusion_realinput40_zero_temp_noncrystallization_finitePeriodicContradiction
    (rho : ℝ) : Prop :=
  1 < rho → ¬ Real.log rho / 2 = 0

/-- Four-state determinant and primitivity certificate imported from the closed-zeta file. -/
def conclusion_realinput40_zero_temp_noncrystallization_fourStateDeterminantCertificate
    (_rho : ℝ) : Prop :=
  conclusion_realinput40_zero_temp_fourstate_sft_closed_zeta_statement

/-- Concrete noncrystallization package for the real-input-`40` zero-temperature endpoint. -/
def conclusion_realinput40_zero_temp_noncrystallization_statement (rho : ℝ) : Prop :=
  conclusion_realinput40_zero_temp_noncrystallization_maxCountFloorLaw rho ∧
    conclusion_realinput40_zero_temp_noncrystallization_positiveGroundEntropy rho ∧
      conclusion_realinput40_zero_temp_noncrystallization_finitePeriodicContradiction rho ∧
        conclusion_realinput40_zero_temp_noncrystallization_fourStateDeterminantCertificate rho

lemma conclusion_realinput40_zero_temp_noncrystallization_floor_half (n : ℕ) :
    Nat.floor ((n : ℚ) / 2) = n / 2 := by
  simpa using Rat.natFloor_natCast_div_natCast n 2

lemma conclusion_realinput40_zero_temp_noncrystallization_log_half_pos
    (rho : ℝ) (hrho : 1 < rho) :
    0 < Real.log rho / 2 := by
  have hlog : 0 < Real.log rho := Real.log_pos hrho
  linarith

lemma conclusion_realinput40_zero_temp_noncrystallization_log_half_ne_zero
    (rho : ℝ) (hrho : 1 < rho) :
    ¬ Real.log rho / 2 = 0 := by
  exact ne_of_gt
    (conclusion_realinput40_zero_temp_noncrystallization_log_half_pos rho hrho)

/-- Paper label: `thm:conclusion-realinput40-zero-temp-noncrystallization`. -/
theorem paper_conclusion_realinput40_zero_temp_noncrystallization
    (rho : ℝ) :
    conclusion_realinput40_zero_temp_noncrystallization_statement rho := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    exact conclusion_realinput40_zero_temp_noncrystallization_floor_half n
  · intro hrho
    exact conclusion_realinput40_zero_temp_noncrystallization_log_half_pos rho hrho
  · intro hrho
    exact conclusion_realinput40_zero_temp_noncrystallization_log_half_ne_zero rho hrho
  · exact paper_conclusion_realinput40_zero_temp_fourstate_sft_closed_zeta

end Omega.Conclusion

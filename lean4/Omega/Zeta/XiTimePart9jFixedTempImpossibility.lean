import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete black-box controller data for
`thm:xi-time-part9j-fixed-temp-impossibility`.

The all-`2` transcript succeeds on `N = 1`; deterministic branch equality makes the same transcript
produce the same output on `N = p`, where the required answer is different. -/
structure xi_time_part9j_fixed_temp_impossibility_data where
  p : ℕ
  callsOnOne : ℕ
  u0 : ℝ
  hu0 : 0 < u0
  controllerOutputOnAllTwos : ℕ → ℕ
  correctIndex : ℕ → ℕ
  correctIndexOne : correctIndex 1 = 1
  correctIndexP : correctIndex p = 2
  allTwosForcesSuccessOnOne : controllerOutputOnAllTwos 1 = correctIndex 1
  deterministicBranchEquality : controllerOutputOnAllTwos p = controllerOutputOnAllTwos 1

namespace xi_time_part9j_fixed_temp_impossibility_data

/-- Probability of the all-`2` transcript under the positive-temperature two-instruction gate. -/
noncomputable def allTwosTranscriptProbability
    (D : xi_time_part9j_fixed_temp_impossibility_data) : ℝ :=
  (D.u0 / (1 + D.u0)) ^ D.callsOnOne

/-- Positive probability of a transcript on which the deterministic branch outputs the wrong
index at `N = p`. -/
def fixed_positive_temperature_zero_error_impossible
    (D : xi_time_part9j_fixed_temp_impossibility_data) : Prop :=
  0 < D.allTwosTranscriptProbability ∧
    D.controllerOutputOnAllTwos D.p ≠ D.correctIndex D.p

end xi_time_part9j_fixed_temp_impossibility_data

/-- Paper label: `thm:xi-time-part9j-fixed-temp-impossibility`. -/
theorem paper_xi_time_part9j_fixed_temp_impossibility
    (D : xi_time_part9j_fixed_temp_impossibility_data) :
    D.fixed_positive_temperature_zero_error_impossible := by
  constructor
  · have hden : 0 < 1 + D.u0 := by linarith [D.hu0]
    have hstep : 0 < D.u0 / (1 + D.u0) := div_pos D.hu0 hden
    simpa [xi_time_part9j_fixed_temp_impossibility_data.allTwosTranscriptProbability]
      using pow_pos hstep D.callsOnOne
  · intro hsame
    have hout : D.controllerOutputOnAllTwos D.p = 1 := by
      rw [D.deterministicBranchEquality, D.allTwosForcesSuccessOnOne, D.correctIndexOne]
    have hbad : (1 : ℕ) = 2 := by
      calc
        1 = D.controllerOutputOnAllTwos D.p := hout.symm
        _ = D.correctIndex D.p := hsame
        _ = 2 := D.correctIndexP
    omega

end Omega.Zeta

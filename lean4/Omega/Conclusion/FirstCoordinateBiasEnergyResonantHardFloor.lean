import Mathlib.Tactic
import Omega.Conclusion.FoldGoldenResonanceCollisionGapHardFloor

namespace Omega.Conclusion

noncomputable section

/-- The retained left Fibonacci resonance amplitude for the first-coordinate bias floor. -/
def conclusion_first_coordinate_bias_energy_resonant_hard_floor_left_mode : ℝ :=
  singlepairResonanceConstant

/-- The retained right Fibonacci resonance amplitude for the first-coordinate bias floor. -/
def conclusion_first_coordinate_bias_energy_resonant_hard_floor_right_mode : ℝ :=
  singlepairResonanceConstant

/-- The first-coordinate bias energy after multiplying by the ambient Fibonacci scale. -/
def conclusion_first_coordinate_bias_energy_resonant_hard_floor_scaled_energy
    (m : ℕ) : ℝ :=
  foldbinScaledCollisionExcess
      conclusion_fold_golden_resonance_collision_gap_hard_floor_toyCol m /
    4

/-- The hard floor obtained by retaining the two Fibonacci resonance modes. -/
def conclusion_first_coordinate_bias_energy_resonant_hard_floor_floor : ℝ :=
  (conclusion_first_coordinate_bias_energy_resonant_hard_floor_left_mode ^ (2 : ℕ) +
      conclusion_first_coordinate_bias_energy_resonant_hard_floor_right_mode ^ (2 : ℕ)) /
    4

/-- Paper-facing concrete statement for the first-coordinate resonant hard floor. -/
def conclusion_first_coordinate_bias_energy_resonant_hard_floor_statement : Prop :=
  (∀ m : ℕ,
      conclusion_first_coordinate_bias_energy_resonant_hard_floor_floor ≤
        conclusion_first_coordinate_bias_energy_resonant_hard_floor_scaled_energy m) ∧
    0 < conclusion_first_coordinate_bias_energy_resonant_hard_floor_floor

/-- Paper label: `thm:conclusion-first-coordinate-bias-energy-resonant-hard-floor`. -/
theorem paper_conclusion_first_coordinate_bias_energy_resonant_hard_floor :
    conclusion_first_coordinate_bias_energy_resonant_hard_floor_statement := by
  refine ⟨?_, ?_⟩
  · intro m
    have hcollision := paper_conclusion_fold_golden_resonance_collision_gap_hard_floor m
    unfold conclusion_first_coordinate_bias_energy_resonant_hard_floor_floor
      conclusion_first_coordinate_bias_energy_resonant_hard_floor_scaled_energy
      conclusion_first_coordinate_bias_energy_resonant_hard_floor_left_mode
      conclusion_first_coordinate_bias_energy_resonant_hard_floor_right_mode
    nlinarith
  · unfold conclusion_first_coordinate_bias_energy_resonant_hard_floor_floor
      conclusion_first_coordinate_bias_energy_resonant_hard_floor_left_mode
      conclusion_first_coordinate_bias_energy_resonant_hard_floor_right_mode
      singlepairResonanceConstant
    norm_num

end

end Omega.Conclusion

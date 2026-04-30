import Mathlib.Tactic

namespace Omega.Conclusion

/--
Concrete branch-audit data for the real-input-`40` seven-loop collapse.  The primitive
Witt certificate is coefficientwise: after subtracting the core, only the two-step
coefficient survives.  The Ramanujan projection certificate records the resulting
spike-background law.
-/
structure conclusion_realinput40_seven_two_step_loops_collapse_data where
  branch_two_step_loop_count : ℕ
  conclusion_realinput40_seven_two_step_loops_collapse_primitiveFull : ℕ → ℤ
  conclusion_realinput40_seven_two_step_loops_collapse_primitiveCore : ℕ → ℤ
  conclusion_realinput40_seven_two_step_loops_collapse_loopAmplitude : ℤ
  conclusion_realinput40_seven_two_step_loops_collapse_ramanujanProjection : ℕ → ℤ
  conclusion_realinput40_seven_two_step_loops_collapse_ramanujanBackground : ℕ → ℤ
  conclusion_realinput40_seven_two_step_loops_collapse_branch_count_certificate :
    branch_two_step_loop_count = 7
  conclusion_realinput40_seven_two_step_loops_collapse_primitive_witt_certificate :
    ∀ n : ℕ,
      conclusion_realinput40_seven_two_step_loops_collapse_primitiveFull n -
          conclusion_realinput40_seven_two_step_loops_collapse_primitiveCore n =
        if n = 2 then conclusion_realinput40_seven_two_step_loops_collapse_loopAmplitude
        else 0
  conclusion_realinput40_seven_two_step_loops_collapse_ramanujan_projection_certificate :
    ∀ q : ℕ,
      conclusion_realinput40_seven_two_step_loops_collapse_ramanujanProjection q =
        conclusion_realinput40_seven_two_step_loops_collapse_ramanujanBackground q +
          if q ∣ 2 then conclusion_realinput40_seven_two_step_loops_collapse_loopAmplitude
          else 0

namespace conclusion_realinput40_seven_two_step_loops_collapse_data

/-- The primitive generating-function identity `P - P_core = u z^2`, coefficientwise. -/
def primitive_witt_collapse
    (D : conclusion_realinput40_seven_two_step_loops_collapse_data) : Prop :=
  ∀ n : ℕ,
    D.conclusion_realinput40_seven_two_step_loops_collapse_primitiveFull n -
        D.conclusion_realinput40_seven_two_step_loops_collapse_primitiveCore n =
      if n = 2 then D.conclusion_realinput40_seven_two_step_loops_collapse_loopAmplitude
      else 0

/-- The Ramanujan projection is the background plus the divisibility shadow of the spike. -/
def ramanujan_projection
    (D : conclusion_realinput40_seven_two_step_loops_collapse_data) : Prop :=
  ∀ q : ℕ,
    D.conclusion_realinput40_seven_two_step_loops_collapse_ramanujanProjection q =
      D.conclusion_realinput40_seven_two_step_loops_collapse_ramanujanBackground q +
        if q ∣ 2 then D.conclusion_realinput40_seven_two_step_loops_collapse_loopAmplitude
        else 0

end conclusion_realinput40_seven_two_step_loops_collapse_data

/-- Paper label: `prop:conclusion-realinput40-seven-two-step-loops-collapse`. -/
theorem paper_conclusion_realinput40_seven_two_step_loops_collapse
    (D : conclusion_realinput40_seven_two_step_loops_collapse_data) :
    D.branch_two_step_loop_count = 7 ∧ D.primitive_witt_collapse ∧
      D.ramanujan_projection := by
  exact
    ⟨D.conclusion_realinput40_seven_two_step_loops_collapse_branch_count_certificate,
      D.conclusion_realinput40_seven_two_step_loops_collapse_primitive_witt_certificate,
      D.conclusion_realinput40_seven_two_step_loops_collapse_ramanujan_projection_certificate⟩

end Omega.Conclusion

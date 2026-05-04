import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete data for the single-hole screen closure criterion.  The exactification identity
identifies deficit with top Betti number, unit deficit has a one-face descent witness, and the
one-face law prevents a zero target from being reached from any deficit except `1`. -/
structure conclusion_screen_single_hole_one_step_closure_Data where
  conclusion_screen_single_hole_one_step_closure_screen : Type*
  conclusion_screen_single_hole_one_step_closure_face : Type*
  conclusion_screen_single_hole_one_step_closure_deficit :
    conclusion_screen_single_hole_one_step_closure_screen → ℕ
  conclusion_screen_single_hole_one_step_closure_topBetti :
    conclusion_screen_single_hole_one_step_closure_screen → ℕ
  conclusion_screen_single_hole_one_step_closure_mem :
    conclusion_screen_single_hole_one_step_closure_face →
      conclusion_screen_single_hole_one_step_closure_screen → Prop
  conclusion_screen_single_hole_one_step_closure_insert :
    conclusion_screen_single_hole_one_step_closure_screen →
      conclusion_screen_single_hole_one_step_closure_face →
        conclusion_screen_single_hole_one_step_closure_screen
  conclusion_screen_single_hole_one_step_closure_exactification :
    ∀ S,
      conclusion_screen_single_hole_one_step_closure_deficit S =
        conclusion_screen_single_hole_one_step_closure_topBetti S
  conclusion_screen_single_hole_one_step_closure_unitDescent :
    ∀ S,
      conclusion_screen_single_hole_one_step_closure_deficit S = 1 →
        ∃ f,
          ¬ conclusion_screen_single_hole_one_step_closure_mem f S ∧
            conclusion_screen_single_hole_one_step_closure_deficit
              (conclusion_screen_single_hole_one_step_closure_insert S f) = 0
  conclusion_screen_single_hole_one_step_closure_oneFaceZeroOneGain :
    ∀ S f,
      ¬ conclusion_screen_single_hole_one_step_closure_mem f S →
        conclusion_screen_single_hole_one_step_closure_deficit
            (conclusion_screen_single_hole_one_step_closure_insert S f) = 0 →
          conclusion_screen_single_hole_one_step_closure_deficit S = 1

/-- Paper label: `cor:conclusion-screen-single-hole-one-step-closure`. -/
theorem paper_conclusion_screen_single_hole_one_step_closure
    (D : conclusion_screen_single_hole_one_step_closure_Data)
    (S : D.conclusion_screen_single_hole_one_step_closure_screen) :
    (D.conclusion_screen_single_hole_one_step_closure_deficit S = 1 ↔
        D.conclusion_screen_single_hole_one_step_closure_topBetti S = 1) ∧
      (D.conclusion_screen_single_hole_one_step_closure_deficit S = 1 ↔
        ∃ f,
          ¬ D.conclusion_screen_single_hole_one_step_closure_mem f S ∧
            D.conclusion_screen_single_hole_one_step_closure_deficit
              (D.conclusion_screen_single_hole_one_step_closure_insert S f) = 0) := by
  refine ⟨?_, ?_⟩
  · constructor
    · intro hdeficit
      rw [← D.conclusion_screen_single_hole_one_step_closure_exactification S]
      exact hdeficit
    · intro hbetti
      rw [D.conclusion_screen_single_hole_one_step_closure_exactification S]
      exact hbetti
  · constructor
    · exact D.conclusion_screen_single_hole_one_step_closure_unitDescent S
    · rintro ⟨f, hfnot, hzero⟩
      exact D.conclusion_screen_single_hole_one_step_closure_oneFaceZeroOneGain S f hfnot hzero

end Omega.Conclusion

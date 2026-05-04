import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-single-hidden-phase-transition-exact-inversion`. -/
theorem paper_conclusion_single_hidden_phase_transition_exact_inversion {n : ℕ}
    {a τ w1 w2 : ℝ} (ha : 0 < a)
    (hw1 : w1 = a * ((n : ℝ) + 1 - τ)) (hw2 : w2 = a * (τ - (n : ℝ))) :
    a = w1 + w2 ∧ τ = (n : ℝ) + w2 / (w1 + w2) := by
  have hsum : w1 + w2 = a := by
    rw [hw1, hw2]
    ring
  have hτsub : τ - (n : ℝ) = w2 / a := by
    rw [hw2]
    field_simp [ha.ne']
  constructor
  · exact hsum.symm
  · calc
      τ = (n : ℝ) + (τ - (n : ℝ)) := by ring
      _ = (n : ℝ) + w2 / a := by rw [hτsub]
      _ = (n : ℝ) + w2 / (w1 + w2) := by rw [hsum]

end Omega.Conclusion

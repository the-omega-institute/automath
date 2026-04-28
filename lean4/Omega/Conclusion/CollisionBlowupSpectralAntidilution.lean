import Mathlib.Tactic
import Omega.Conclusion.BinfoldCollisionScaleForcesMaxfiberDivergence

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-collision-blowup-spectral-antidilution`. -/
theorem paper_conclusion_collision_blowup_spectral_antidilution (M Z : ℕ → ℕ)
    (Col : ℕ → ℝ)
    (hbound :
      ∀ m, binfoldCollisionScaleTerm (fun n => (M n : ℝ)) Col m ≤
        (M m : ℝ) - (Z m : ℝ))
    (hdiv : NatDivergesToInfinity (binfoldCollisionScaleTerm (fun n => (M n : ℝ)) Col))
    (l2Surrogate : Prop) (hnoL2 : ¬ l2Surrogate) :
    (∀ m, binfoldCollisionScaleTerm (fun n => (M n : ℝ)) Col m ≤
        (M m : ℝ) - (Z m : ℝ)) ∧
      NatDivergesToInfinity (fun m => (M m : ℝ) - (Z m : ℝ)) ∧
        ¬ l2Surrogate := by
  refine ⟨hbound, ?_, hnoL2⟩
  intro K
  obtain ⟨m, hm⟩ := hdiv K
  exact ⟨m, hm.trans (hbound m)⟩

end Omega.Conclusion

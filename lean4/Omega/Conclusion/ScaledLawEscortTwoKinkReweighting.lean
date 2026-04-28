import Mathlib.Tactic
import Omega.Conclusion.EscortTwoStateClosure

namespace Omega.Conclusion

noncomputable section

/-- The escort-scaled two-kink recoverability profile. -/
def conclusion_scaled_law_escort_two_kink_reweighting_profile (q : ℕ) (τ : ℝ) : ℝ :=
  (1 - Omega.Conclusion.conclusion_escort_two_state_closure_theta q) * min 1 τ +
    Omega.Conclusion.conclusion_escort_two_state_closure_theta q * min 1 (Real.goldenRatio * τ)

/-- The fixed kink locations of the escort-scaled law. -/
def conclusion_scaled_law_escort_two_kink_reweighting_breakpoints : ℝ × ℝ :=
  (1 / Real.goldenRatio, 1)

/-- Paper label: `thm:conclusion-scaled-law-escort-two-kink-reweighting`. -/
theorem paper_conclusion_scaled_law_escort_two_kink_reweighting (q : ℕ) (τ : ℝ) :
    conclusion_scaled_law_escort_two_kink_reweighting_profile q τ =
        (1 - Omega.Conclusion.conclusion_escort_two_state_closure_theta q) * min 1 τ +
          Omega.Conclusion.conclusion_escort_two_state_closure_theta q *
            min 1 (Real.goldenRatio * τ) ∧
      conclusion_scaled_law_escort_two_kink_reweighting_breakpoints =
        (1 / Real.goldenRatio, 1) := by
  exact ⟨rfl, rfl⟩

end

end Omega.Conclusion

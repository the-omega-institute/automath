import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-realinput40-branch-radius-certificate-blind-to-first-rh-failure`. -/
theorem paper_conclusion_realinput40_branch_radius_certificate_blind_to_first_rh_failure
    (thetaR Rtheta : Real) (branchDetector sharpFailure : Real → Prop) (hgap : thetaR < Rtheta)
    (hblind : ∀ θ, thetaR < θ → θ < Rtheta → ¬ branchDetector θ)
    (hfail : ∀ θ, thetaR < θ → θ < Rtheta → sharpFailure θ) :
    ∃ θ, sharpFailure θ ∧ ¬ branchDetector θ := by
  refine ⟨(thetaR + Rtheta) / 2, ?_⟩
  have hleft : thetaR < (thetaR + Rtheta) / 2 := by linarith
  have hright : (thetaR + Rtheta) / 2 < Rtheta := by linarith
  exact ⟨hfail _ hleft hright, hblind _ hleft hright⟩

end Omega.Conclusion

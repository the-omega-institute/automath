import Mathlib.Data.Real.Basic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9pb-rh-transition-analytic-not-branch`. -/
theorem paper_xi_time_part9pb_rh_transition_analytic_not_branch
    (thetaR Rtheta gap : ℝ)
    (positiveAxisNoBranch analyticInterior spectralCrossing : Prop)
    (hNoBranch : positiveAxisNoBranch)
    (hGap : gap = Rtheta - thetaR)
    (hGapPos : 0 < gap)
    (hInterior : thetaR < Rtheta → analyticInterior)
    (hTheta : thetaR < Rtheta)
    (hCross : spectralCrossing) :
    positiveAxisNoBranch ∧ analyticInterior ∧ 0 < gap ∧ spectralCrossing := by
  have hGapPositive : 0 < gap := by
    simpa [hGap] using hGapPos
  exact ⟨hNoBranch, hInterior hTheta, hGapPositive, hCross⟩

end Omega.Zeta

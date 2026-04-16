import Mathlib.Tactic

namespace Omega.CircleDimension

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the symmetric-channel corollary in the mode
    space reconstruction section.
    cor:poisson-symmetrization -/
theorem paper_circle_dimension_poisson_symmetrization
    (twoChannelHypotheses aRecoversCenteredSymmetrization laplaceInvertsSymmetrization : Prop)
    (hA : twoChannelHypotheses → aRecoversCenteredSymmetrization)
    (hLaplace : aRecoversCenteredSymmetrization → laplaceInvertsSymmetrization) :
    twoChannelHypotheses →
      aRecoversCenteredSymmetrization ∧ laplaceInvertsSymmetrization := by
  intro hHyp
  have hSymm : aRecoversCenteredSymmetrization := hA hHyp
  exact ⟨hSymm, hLaplace hSymm⟩

end Omega.CircleDimension

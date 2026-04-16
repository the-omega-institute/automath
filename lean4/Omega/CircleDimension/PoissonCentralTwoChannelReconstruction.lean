import Mathlib.Tactic

namespace Omega.CircleDimension

set_option maxHeartbeats 400000 in
/-- Paper-facing wrapper for centered Poisson two-channel reconstruction via the Cauchy transform
    and Stieltjes inversion.
    prop:cdim-poisson-central-two-channel-reconstruction -/
theorem paper_cdim_poisson_central_two_channel_reconstruction
    (twoChannelCenterReadout cauchyTransformRecovery stieltjesInversion : Prop)
    (hReadout : twoChannelCenterReadout)
    (hRecover : twoChannelCenterReadout → cauchyTransformRecovery)
    (hInvert : cauchyTransformRecovery → stieltjesInversion) :
    twoChannelCenterReadout ∧ cauchyTransformRecovery ∧ stieltjesInversion := by
  have hCauchy : cauchyTransformRecovery := hRecover hReadout
  exact ⟨hReadout, hCauchy, hInvert hCauchy⟩

end Omega.CircleDimension

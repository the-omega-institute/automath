import Mathlib.Tactic
import Omega.CircleDimension.PoissonCentralTwoChannelReconstruction

namespace Omega.CircleDimension

set_option maxHeartbeats 400000 in
/-- Paper-facing wrapper for promoting local two-channel agreement on a nonempty open interval to
    global agreement on the positive imaginary axis, then invoking the centered two-channel
    reconstruction package.
    cor:cdim-poisson-central-two-channel-local-uniqueness -/
theorem paper_cdim_poisson_central_two_channel_local_uniqueness
    (localTwoChannelAgreement globalTwoChannelAgreement equalMeasures : Prop)
    (hAnalytic : localTwoChannelAgreement -> globalTwoChannelAgreement)
    (hGlobal : globalTwoChannelAgreement -> equalMeasures) :
    localTwoChannelAgreement -> equalMeasures := by
  intro hLocal
  exact hGlobal (hAnalytic hLocal)

end Omega.CircleDimension

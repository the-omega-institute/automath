import Mathlib.Data.Real.Basic
import Omega.TypedAddressBiaxialCompletion.BoundaryBlindspot

namespace Omega.TypedAddressBiaxialCompletion

set_option maxHeartbeats 400000 in
/-- If the available radius budget never crosses the target threshold, no exclusion certificate can
be produced.
    cor:typed-address-biaxial-completion-boundary-radius-role -/
theorem paper_typed_address_biaxial_completion_boundary_radius_role
    {rhoMax rhoTarget : ℝ} {canExclude : Prop}
    (hBlindspot : rhoMax <= rhoTarget -> ¬ canExclude)
    (hThreshold : rhoMax <= rhoTarget) :
    ¬ canExclude := by
  exact hBlindspot hThreshold

end Omega.TypedAddressBiaxialCompletion

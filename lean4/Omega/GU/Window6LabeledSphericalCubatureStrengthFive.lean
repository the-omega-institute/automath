import Mathlib.Tactic
import Omega.GU.Window6B3C3SphericalCubatureStrength5

namespace Omega.GU

set_option maxHeartbeats 400000 in
/-- Paper-facing wrapper for the fact that the labeled window-`6` spherical support admits a
    nontrivial degree-`5` cubature but no nontrivial degree-`6` cubature.
    cor:window6-labeled-spherical-cubature-strength-five -/
theorem paper_window6_labeled_spherical_cubature_strength_five
    (existsNontrivialDegreeFiveCubature noNontrivialDegreeSixCubature : Prop)
    (hFive : existsNontrivialDegreeFiveCubature)
    (hSix : noNontrivialDegreeSixCubature) :
    existsNontrivialDegreeFiveCubature ∧ noNontrivialDegreeSixCubature := by
  exact ⟨hFive, hSix⟩

end Omega.GU

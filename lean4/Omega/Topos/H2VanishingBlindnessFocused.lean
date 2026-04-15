import Omega.Topos.H2VanishingBlindness

namespace Omega.Topos

set_option maxHeartbeats 400000 in
/-- Focused-publication wrapper for the `H_2`-vanishing blindness corollary.
    cor:h2-vanishing-blindness -/
theorem paper_conservative_extension_h2_vanishing_blindness_focused
    (H2Zero evZero kernelZero visibleAll blind : Prop)
    (hcollapse : H2Zero → evZero ∧ kernelZero ∧ visibleAll)
    (hblind : evZero → blind) :
    H2Zero → evZero ∧ kernelZero ∧ visibleAll ∧ blind :=
  paper_gluing_failure_h2_vanishing_blindness
    H2Zero evZero kernelZero visibleAll blind hcollapse hblind

end Omega.Topos

import Mathlib.Tactic
import Omega.DerivedConsequences.DerivedWindow6B3C3RootcloudIsotropicDesign

namespace Omega.Zeta

/-- Paper label: `thm:xi-window6-b3c3-weyl-invariant-image-quadratic`. The explicit
window-`6` `B₃/C₃` root clouds split into their two Weyl orbits by squared norm. -/
theorem paper_xi_window6_b3c3_weyl_invariant_image_quadratic :
    ((Omega.DerivedConsequences.derived_window6_b3c3_rootcloud_isotropic_design_b3_roots.filter (fun r => decide (Omega.GU.weightNormSq r = 1))).length = 6) ∧ ((Omega.DerivedConsequences.derived_window6_b3c3_rootcloud_isotropic_design_b3_roots.filter (fun r => decide (Omega.GU.weightNormSq r = 2))).length = 12) ∧ ((Omega.DerivedConsequences.derived_window6_b3c3_rootcloud_isotropic_design_c3_roots.filter (fun r => decide (Omega.GU.weightNormSq r = 2))).length = 12) ∧ ((Omega.DerivedConsequences.derived_window6_b3c3_rootcloud_isotropic_design_c3_roots.filter (fun r => decide (Omega.GU.weightNormSq r = 4))).length = 6) := by
  native_decide

end Omega.Zeta

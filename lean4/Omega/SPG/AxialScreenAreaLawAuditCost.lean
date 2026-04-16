import Omega.SPG.CoordinateBundleScreenCount

namespace Omega.SPG

set_option maxHeartbeats 400000 in
/-- Axial-screen specialization of the coordinate-bundle screen cost formulas.
    prop:spg-axial-screen-area-law-audit-cost -/
theorem paper_spg_axial_screen_area_law_audit_cost (m n : ℕ) :
    Omega.SPG.CoordinateBundleScreenCount.screenComponentCount m n 1 =
        2 ^ (m * (n - 1)) + 1 ∧
      Omega.SPG.CoordinateBundleScreenCount.auditCost m n 1 =
        2 ^ (m * (n - 1)) := by
  simpa using
    Omega.SPG.CoordinateBundleScreenCount.paper_spg_internal_coordinate_bundle_screen_cost_closed_form
      m n 1

end Omega.SPG

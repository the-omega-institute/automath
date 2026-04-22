import Omega.SPG.CoordinateBundleScreenCount

namespace Omega.SPG

/-- Specializing the coordinate-bundle closed forms at `s = n` leaves a single internal connected
component defect and unit audit cost.
    cor:spg-full-internal-screen-one-defect-boundary-closure -/
theorem paper_spg_full_internal_screen_one_defect_boundary_closure (m n : ℕ) :
    Omega.SPG.CoordinateBundleScreenCount.screenComponentCount m n n = 2 ∧
      Omega.SPG.CoordinateBundleScreenCount.auditCost m n n = 1 := by
  simpa using
    Omega.SPG.CoordinateBundleScreenCount.paper_spg_internal_coordinate_bundle_screen_cost_closed_form
      m n n

end Omega.SPG

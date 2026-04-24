import Omega.SPG.CoordinateBundleScreenCount

namespace Omega.Conclusion

open Omega.SPG.CoordinateBundleScreenCount

/-- The chapter-local audit gap `δ_J` is the SPG internal screen audit cost. -/
def coordinateBundleAuditGap (m n s : ℕ) : ℕ :=
  auditCost m n s

/-- Paper label: `thm:conclusion-coordinatebundle-codimension-exponential-defect`. -/
theorem paper_conclusion_coordinatebundle_codimension_exponential_defect (m n s : ℕ) :
    coordinateBundleAuditGap m n s = 2 ^ (m * (n - s)) := by
  simpa [coordinateBundleAuditGap] using
    (paper_spg_internal_coordinate_bundle_screen_cost_closed_form m n s).2

end Omega.Conclusion

import Omega.SPG.AxialScreenAreaLawAuditCost

namespace Omega.Conclusion

/-- Paper-facing conclusion corollary: the axial-screen audit cost is exactly the codimension-one
area law.
    cor:conclusion-fixedresolution-axial-screen-corank-area-law -/
theorem paper_conclusion_fixedresolution_axial_screen_corank_area_law (m n : ℕ) :
    Omega.SPG.CoordinateBundleScreenCount.auditCost m n 1 = 2 ^ (m * (n - 1)) := by
  simpa using (Omega.SPG.paper_spg_axial_screen_area_law_audit_cost m n).2

end Omega.Conclusion

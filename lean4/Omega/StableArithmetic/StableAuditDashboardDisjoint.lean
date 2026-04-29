import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace Omega.StableArithmetic

theorem paper_stable_audit_stable_dashboard_disjoint
    (stableMissing dashboardUnknowns : Finset String) (hcard : dashboardUnknowns.card = 498)
    (hdisjoint : stableMissing ∩ dashboardUnknowns = ∅) :
    (stableMissing ∩ dashboardUnknowns).card = 0 := by
  have _ : dashboardUnknowns.card = 498 := hcard
  simp [hdisjoint]

end Omega.StableArithmetic

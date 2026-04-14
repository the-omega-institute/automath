import Omega.SPG.CoordinateBundleScreenCount

namespace Omega.SPG.CoordinateBundleScreenClosure

open Omega.SPG.CoordinateBundleScreenCount

/-- Paper seeds for the internal coordinate bundle screen closure formulas.
    thm:spg-internal-coordinate-bundle-screen-cost-closed-form -/
theorem paper_spg_internal_coordinate_bundle_screen_cost_closed_form_seeds (m n s : ℕ) :
    screenComponentCount m n s = (2 ^ m) ^ (n - s) + 1 ∧
    auditCost m n s = screenComponentCount m n s - 1 ∧
    auditCost m n s = 2 ^ (m * (n - s)) := by
  refine ⟨screenComponentCount_eq_complement_plus_one m n s, auditCost_eq_count_sub_one m n s, ?_⟩
  rfl

/-- Paper package for the internal coordinate bundle screen closure formulas.
    thm:spg-internal-coordinate-bundle-screen-cost-closed-form -/
theorem paper_spg_internal_coordinate_bundle_screen_cost_closed_form_package (m n s : ℕ) :
    screenComponentCount m n s = (2 ^ m) ^ (n - s) + 1 ∧
    auditCost m n s = screenComponentCount m n s - 1 ∧
    auditCost m n s = 2 ^ (m * (n - s)) :=
  paper_spg_internal_coordinate_bundle_screen_cost_closed_form_seeds m n s

end Omega.SPG.CoordinateBundleScreenClosure

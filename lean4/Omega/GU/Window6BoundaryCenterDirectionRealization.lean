import Mathlib.Tactic
import Omega.GU.Window6BoundaryDyadicDirectionFlag

namespace Omega.GU

/-- The audited boundary-center realization consists exactly of the three rigid dyadic directions,
with the expected support cardinalities. -/
theorem paper_window6_boundary_center_direction_realization :
    _root_.Omega.GU.boundaryDirectionsLinearlyIndependent ∧
      (_root_.Omega.GU.boundaryDirectionSupport 34).card = 2 ∧
      (_root_.Omega.GU.boundaryDirectionSupport 38).card = 3 ∧
      (_root_.Omega.GU.boundaryDirectionSupport 62).card = 5 := by
  refine ⟨_root_.paper_window6_boundary_dyadic_direction_flag.2.2.2, ?_, ?_, ?_⟩
  all_goals native_decide

end Omega.GU

import Mathlib.Tactic
import Omega.EA.FoldWindow6CenterThreeObservablesDimensionDefect

namespace Omega.EA

/-- Concrete center-resolution criterion extracted from the audited window-`6` sector bounds.
The generated center from the three observables resolves at most `12` dimensions out of the full
`21`, and equality in the four-sector count is equivalent to saturating each sector bound. -/
def foldCenterResolutionCriterionIndwEpsClaim : Prop :=
  0 < cFiberHist 6 2 ∧
    1 < cFiberHist 6 3 ∧
    0 < cFiberHist 6 4 ∧
    foldWindow6CenterThreeObservablesResolvedDimension = 12 ∧
    momentSum 0 6 = 21 ∧
    foldWindow6CenterThreeObservablesDimensionDefect = 9 ∧
    ∀ a b c d : ℕ, a ≤ 2 → b ≤ 3 → c ≤ 3 → d ≤ 4 →
      (a + b + c + d = 12 ↔ a = 2 ∧ b = 3 ∧ c = 3 ∧ d = 4)

/-- Paper label: `prop:fold-center-resolution-criterion-indw-eps`. In the audited window-`6`
instance, the three central observables resolve `12` dimensions, leave defect `9`, and the
sectorwise saturation criterion is exactly the arithmetic equality case for the four sector bounds.
-/
theorem paper_fold_center_resolution_criterion_indw_eps :
    foldCenterResolutionCriterionIndwEpsClaim := by
  exact paper_fold_window6_center_three_observables_dimension_defect

end Omega.EA

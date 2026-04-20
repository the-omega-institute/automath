import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace Omega.GU

/-- The boundary-tower sum-12 classification allows exactly the three audited resolutions
`{4, 6, 8}`. -/
def boundaryTowerSum12AdmissibleResolutions : Finset Nat :=
  ([4, 6, 8] : List Nat).toFinset

/-- The order-12 unit-group classification allows exactly the two audited resolutions `{5, 6}`. -/
def order12UnitGroupAdmissibleResolutions : Finset Nat :=
  ([5, 6] : List Nat).toFinset

/-- The two audited resolution lists intersect uniquely at `m = 6`.
    cor:double-12-constraints-unique-intersection-m6 -/
theorem paper_double_12_constraints_unique_intersection_m6 :
    boundaryTowerSum12AdmissibleResolutions ∩ order12UnitGroupAdmissibleResolutions =
      (([6] : List Nat).toFinset) := by
  decide

end Omega.GU

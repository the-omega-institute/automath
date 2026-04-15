import Mathlib

namespace Omega.CircleDimension

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the entropy identity in Cayley coordinates.
    thm:precision-ledger -/
theorem paper_circle_dimension_precision_ledger
    (diffEntropyX diffEntropyU precisionPotential : ℝ)
    (hLedger : diffEntropyX = diffEntropyU + precisionPotential) :
    diffEntropyX = diffEntropyU + precisionPotential := by
  exact hLedger

end Omega.CircleDimension

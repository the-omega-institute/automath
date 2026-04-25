import Mathlib.Tactic
import Omega.SyncKernelWeighted.EdgeworthSixEight

namespace Omega.SyncKernelWeighted

/-- Paper label: `cor:edgeworth-fourth`.
The audited variance and fourth cumulant reduce to the recorded rational values, and so do the
normalized fourth cumulant and the corresponding first Edgeworth coefficient. -/
theorem paper_edgeworth_fourth :
    edgeworthSigmaSq = 11 / 102 ∧
      edgeworthKappa4 = 1559 / 58956 ∧
      edgeworthKappa4 / edgeworthSigmaSq ^ 2 = 4677 / 2057 ∧
      edgeworthKappa4 / (24 * edgeworthSigmaSq ^ 2) = 4677 / 49368 := by
  norm_num [edgeworthSigmaSq, edgeworthKappa4]

end Omega.SyncKernelWeighted

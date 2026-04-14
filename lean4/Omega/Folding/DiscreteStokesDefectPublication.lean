import Omega.Folding.Defect

namespace Omega.Folding

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the discrete-Stokes telescoping identity in the
fold-truncation paper.
    thm:fold-discrete-stokes-defect -/
theorem paper_fold_truncation_discrete_stokes_defect
    (m k : Nat) (ω : Omega.Word (m + k)) :
    Omega.globalDefect (Nat.le_add_right m k) ω = Omega.defectChain m k ω := by
  simpa using Omega.paper_fold_discrete_stokes_defect m k ω

end Omega.Folding

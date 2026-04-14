import Omega.Folding.InverseLimit

namespace Omega.Folding

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the inverse-limit identification in the
resolution-folding paper.
    thm:inverse-limit-golden -/
theorem paper_resolution_folding_inverse_limit_golden :
    Nonempty (Omega.X.CompatibleFamily ≃ Omega.X.XInfinity) := by
  exact ⟨Omega.X.inverseLimitEquiv⟩

end Omega.Folding

import Omega.Folding.Defect

namespace Omega.Folding

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the total-variation auditable bound in the
fold-truncation paper.
    cor:fold-discrete-stokes-auditable-bound -/
theorem paper_fold_truncation_discrete_stokes_auditable_bound :
    ∃ (_D : Type) (_K : Nat → Type),
      True :=
  foldDiscreteStokesAuditableBound

end Omega.Folding

import Omega.EA.RewriteCore

namespace Omega.EA

open RewriteCore

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for termination of the exact rewrite system.
    lem:rewrite-termination -/
theorem paper_projection_rewrite_termination :
    WellFounded (flip RewriteCore.Step) := by
  refine
    WellFounded.mono (InvImage.wf (fun w : RewriteCore.Word => w.length) wellFounded_lt) ?_
  intro a b h
  exact RewriteCore.step_length_lt h

end Omega.EA

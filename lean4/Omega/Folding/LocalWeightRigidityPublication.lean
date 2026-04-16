import Omega.Folding.Rewrite

namespace Omega.Folding

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the local weight rigidity lemma in the
    resolution-folding paper.
    lem:local-weight-rigidity -/
theorem paper_resolution_folding_local_weight_rigidity
    {a b : Omega.Rewrite.DigitCfg}
    (hstep : Omega.Rewrite.Step a b) :
    Omega.Rewrite.rankLex b < Omega.Rewrite.rankLex a := by
  exact Omega.Rewrite.step_rankLex hstep

end Omega.Folding

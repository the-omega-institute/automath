import Omega.Topos.UniqueBranchContextualityComparison

namespace Omega.Topos

set_option maxHeartbeats 400000 in
/-- Focused-publication wrapper for the unique-branch contextuality comparison theorem.
    thm:unique-branch-contextuality-comparison -/
theorem paper_conservative_extension_unique_branch_contextuality_comparison_focused
    {State Ref : Type}
    (CompSec Sec NullGlue : State → Ref → Prop)
    (compatibleFamily globalSection : Prop)
    {p : State} {r : Ref}
    (hComp : CompSec p r ↔ compatibleFamily)
    (hSec : Sec p r ↔ globalSection)
    (hNull : NullGlue p r ↔ CompSec p r ∧ ¬ Sec p r) :
    (CompSec p r ↔ compatibleFamily) ∧
      (Sec p r ↔ globalSection) ∧
      (NullGlue p r ↔ compatibleFamily ∧ ¬ globalSection) :=
  paper_gluing_failure_unique_branch_contextuality_comparison
    CompSec Sec NullGlue compatibleFamily globalSection hComp hSec hNull

end Omega.Topos

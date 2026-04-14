import Omega.Topos.SheafLocalToGlobalAPAL

namespace Omega.Topos.GluingFailureSheafLocalToGlobalAPAL

set_option maxHeartbeats 400000 in
/-- Gluing-failure publication wrapper for the sheaf-at-a-reference corollary.
    cor:sheaf-local-to-global -/
theorem paper_gluing_failure_sheaf_local_to_global_apal
    {State Ref Value : Type}
    (CompSec Sec : State → Ref → Prop) (sheafified : State → Ref → Set Value)
    {p : State} (r : Ref)
    (hcompat : CompSec p r ↔ (sheafified p r).Nonempty)
    (hsheaf : Sec p r ↔ (sheafified p r).Nonempty) :
    CompSec p r ↔ Sec p r :=
  Omega.Topos.SheafLocalToGlobalAPAL.paper_conservative_extension_sheaf_local_to_global_apal
    CompSec Sec sheafified r hcompat hsheaf

end Omega.Topos.GluingFailureSheafLocalToGlobalAPAL

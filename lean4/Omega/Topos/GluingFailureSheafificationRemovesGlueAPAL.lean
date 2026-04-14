import Omega.Topos.SheafificationRemovesGlueAPAL

namespace Omega.Topos.GluingFailureSheafificationRemovesGlueAPAL

set_option maxHeartbeats 400000 in
/-- Gluing-failure publication wrapper for the sheafification-removes-glue corollary.
    cor:sheafification-removes-glue -/
theorem paper_gluing_failure_sheafification_removes_glue_apal
    {State Ref Value : Type}
    (CompSec SecSharp : State → Ref → Prop) (sheafified : State → Ref → Set Value)
    {p : State} (r : Ref)
    (hcompat : CompSec p r ↔ (sheafified p r).Nonempty)
    (hsheaf : SecSharp p r ↔ (sheafified p r).Nonempty) :
    CompSec p r ↔ SecSharp p r :=
  Omega.Topos.SheafificationRemovesGlueAPAL.paper_conservative_extension_sheafification_removes_glue_apal
    CompSec SecSharp sheafified r hcompat hsheaf

end Omega.Topos.GluingFailureSheafificationRemovesGlueAPAL

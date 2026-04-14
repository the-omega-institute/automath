import Omega.Topos.SheafificationCharacterization

namespace Omega.Topos.SheafificationRemovesGlueAPAL

set_option maxHeartbeats 400000 in
/-- APAL publication wrapper for the sheafification-removes-glue corollary.
    cor:sheafification-removes-glue -/
theorem paper_conservative_extension_sheafification_removes_glue_apal
    {State Ref Value : Type}
    (CompSec SecSharp : State → Ref → Prop) (sheafified : State → Ref → Set Value)
    {p : State} (r : Ref)
    (hcompat : CompSec p r ↔ (sheafified p r).Nonempty)
    (hsheaf : SecSharp p r ↔ (sheafified p r).Nonempty) :
    CompSec p r ↔ SecSharp p r := by
  constructor
  · intro hComp
    exact hsheaf.mpr
      ((Omega.Topos.paper_conservative_extension_sheafification_characterization_seeds
        CompSec sheafified r hcompat).mp hComp)
  · intro hSec
    exact (Omega.Topos.paper_conservative_extension_sheafification_characterization_seeds
      CompSec sheafified r hcompat).mpr (hsheaf.mp hSec)

end Omega.Topos.SheafificationRemovesGlueAPAL

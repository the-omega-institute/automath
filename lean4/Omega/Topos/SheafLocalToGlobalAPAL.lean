import Omega.Topos.SheafificationCharacterization

namespace Omega.Topos.SheafLocalToGlobalAPAL

set_option maxHeartbeats 400000 in
/-- APAL publication wrapper for the sheaf-at-a-reference corollary.
    cor:sheaf-local-to-global -/
theorem paper_conservative_extension_sheaf_local_to_global_apal
    {State Ref Value : Type}
    (CompSec Sec : State → Ref → Prop) (sheafified : State → Ref → Set Value)
    {p : State} (r : Ref)
    (hcompat : CompSec p r ↔ (sheafified p r).Nonempty)
    (hsheaf : Sec p r ↔ (sheafified p r).Nonempty) :
    CompSec p r ↔ Sec p r := by
  constructor
  · intro hComp
    exact hsheaf.mpr ((Omega.Topos.paper_conservative_extension_sheafification_characterization_seeds
      CompSec sheafified r hcompat).mp hComp)
  · intro hSec
    exact (Omega.Topos.paper_conservative_extension_sheafification_characterization_seeds
      CompSec sheafified r hcompat).mpr (hsheaf.mp hSec)

end Omega.Topos.SheafLocalToGlobalAPAL

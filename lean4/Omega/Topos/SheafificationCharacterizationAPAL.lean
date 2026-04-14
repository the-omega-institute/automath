import Omega.Topos.SheafificationCharacterization

namespace Omega.Topos

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for sheafification characterization in the APAL paper.
    thm:sheafification-characterization -/
theorem paper_conservative_extension_sheafification_characterization_apal
    {State Ref Value : Type}
    (CompSec : State → Ref → Prop) (sheafified : State → Ref → Set Value)
    {p : State} (r : Ref)
    (hcompat : CompSec p r ↔ (sheafified p r).Nonempty) :
    CompSec p r ↔ (sheafified p r).Nonempty :=
  paper_conservative_extension_sheafification_characterization_package
    CompSec sheafified r hcompat

end Omega.Topos

import Omega.Topos.SheafificationCharacterizationAPAL

namespace Omega.Topos.GluingFailureSheafificationCharacterizationAPAL

set_option maxHeartbeats 400000 in
/-- Gluing-failure publication wrapper for sheafification characterization.
    thm:sheafification-characterization -/
theorem paper_gluing_failure_sheafification_characterization_apal
    {State Ref Value : Type}
    (CompSec : State → Ref → Prop) (sheafified : State → Ref → Set Value)
    {p : State} (r : Ref)
    (hcompat : CompSec p r ↔ (sheafified p r).Nonempty) :
    CompSec p r ↔ (sheafified p r).Nonempty :=
  Omega.Topos.paper_conservative_extension_sheafification_characterization_apal
    CompSec sheafified r hcompat

end Omega.Topos.GluingFailureSheafificationCharacterizationAPAL

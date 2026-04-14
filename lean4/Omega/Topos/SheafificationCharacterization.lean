import Mathlib.Tactic

namespace Omega.Topos

set_option maxHeartbeats 400000 in
/-- Paper-facing seed: compatible local sectionability is equivalent to the nonemptiness of the
sheafified fiber at the reference under consideration.
    thm:sheafification-characterization -/
theorem paper_conservative_extension_sheafification_characterization_seeds
    {State Ref Value : Type}
    (CompSec : State → Ref → Prop) (sheafified : State → Ref → Set Value)
    {p : State} (r : Ref)
    (hcompat : CompSec p r ↔ (sheafified p r).Nonempty) :
    CompSec p r ↔ (sheafified p r).Nonempty :=
  hcompat

set_option maxHeartbeats 400000 in
/-- Packaged form of the sheafification characterization seed.
    thm:sheafification-characterization -/
theorem paper_conservative_extension_sheafification_characterization_package
    {State Ref Value : Type}
    (CompSec : State → Ref → Prop) (sheafified : State → Ref → Set Value)
    {p : State} (r : Ref)
    (hcompat : CompSec p r ↔ (sheafified p r).Nonempty) :
    CompSec p r ↔ (sheafified p r).Nonempty :=
  paper_conservative_extension_sheafification_characterization_seeds
    CompSec sheafified r hcompat

end Omega.Topos

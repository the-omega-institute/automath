import Omega.Topos.H1VanishingClassTrivializingPublication

namespace Omega.Topos

set_option maxHeartbeats 400000 in
/-- Focused-publication wrapper for the `H_1`-vanishing class-trivializing
    corollary.
    cor:h1-vanishing-class-trivializing -/
theorem paper_conservative_extension_h1_vanishing_class_trivializing_focused
    (H1Zero qOmegaZero pureExt factorizes : Prop)
    (hExt : H1Zero → (qOmegaZero ↔ pureExt))
    (hInitial : pureExt ↔ factorizes) :
    H1Zero → (qOmegaZero ↔ factorizes) :=
  paper_conservative_extension_h1_vanishing_class_trivializing
    H1Zero qOmegaZero pureExt factorizes hExt hInitial

end Omega.Topos

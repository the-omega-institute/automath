import Omega.Topos.H1FreeNoBlindnessPublication

namespace Omega.Topos

set_option maxHeartbeats 400000 in
/-- Focused-publication wrapper for the `H_1`-free no-blindness corollary.
    cor:h1-free-no-blindness -/
theorem paper_conservative_extension_h1_free_no_blindness_focused
    (omegaZero KZero visiblePartNontrivial properVisibleQuotient singleVisible : Prop)
    (hiff : KZero ↔ omegaZero)
    (hvisible : ¬ omegaZero → visiblePartNontrivial)
    (hproper : singleVisible → ¬ omegaZero → properVisibleQuotient) :
    (KZero ↔ omegaZero) ∧
      (¬ omegaZero → visiblePartNontrivial) ∧
      (singleVisible → ¬ omegaZero → properVisibleQuotient) := by
  exact
    paper_conservative_extension_h1_free_no_blindness
      omegaZero KZero visiblePartNontrivial properVisibleQuotient singleVisible
      hiff hvisible hproper

end Omega.Topos

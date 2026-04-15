import Omega.Topos.H1FreeNoBlindness

namespace Omega.Topos

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the non-focused APAL paper's
    `H_1`-free no-blindness corollary.
    cor:h1-free-no-blindness -/
theorem paper_conservative_extension_h1_free_no_blindness
    (ωZero KZero visiblePartNontrivial properVisibleQuotient singleVisible : Prop)
    (hiff : KZero ↔ ωZero)
    (hvisible : ¬ ωZero → visiblePartNontrivial)
    (hproper : singleVisible → ¬ ωZero → properVisibleQuotient) :
    (KZero ↔ ωZero) ∧
      (¬ ωZero → visiblePartNontrivial) ∧
      (singleVisible → ¬ ωZero → properVisibleQuotient) := by
  have hbase :=
    paper_gluing_failure_h1_free_no_blindness
      ωZero KZero visiblePartNontrivial properVisibleQuotient singleVisible
      hiff
      (fun hK => hvisible fun hω => hK (hiff.mpr hω))
      hproper
  exact ⟨hbase.1, hvisible, hproper⟩

end Omega.Topos

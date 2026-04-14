namespace Omega.Topos

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the `H_1`-free no-blindness corollary.
    cor:h1-free-no-blindness -/
theorem paper_gluing_failure_h1_free_no_blindness
    (ωZero KZero visiblePartNontrivial properVisibleQuotient singleVisible : Prop)
    (hiff : KZero ↔ ωZero)
    (hvisible : ¬ KZero → visiblePartNontrivial)
    (hproper : singleVisible → ¬ ωZero → properVisibleQuotient) :
    (KZero ↔ ωZero) ∧
      (¬ ωZero → visiblePartNontrivial) ∧
      (singleVisible → ¬ ωZero → properVisibleQuotient) := by
  refine ⟨hiff, ?_, hproper⟩
  intro hω
  apply hvisible
  intro hK
  exact hω (hiff.mp hK)

end Omega.Topos

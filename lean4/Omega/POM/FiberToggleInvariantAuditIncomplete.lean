import Omega.POM.FiberSymmetricOrderVisibleLayerSeparation

namespace Omega.POM

/-- Paper label: `cor:pom-fiber-toggle-invariant-audit-incomplete`. -/
theorem paper_pom_fiber_toggle_invariant_audit_incomplete :
    ∃ lengths_x lengths_y : List ℕ,
      symmetricVisibleLayer lengths_x = symmetricVisibleLayer lengths_y ∧
        zigzagComponentLengthMultiset lengths_x ≠ zigzagComponentLengthMultiset lengths_y := by
  refine ⟨[2, 3], [3, 2], ?_⟩
  have hseparation :
      symmetricVisibleLayer [2, 3] = symmetricVisibleLayer [3, 2] ∧
        (⟨[2, 3]⟩ : PomFiberFenceData).hasBirkhoffFenceIdealRepresentation ∧
        (⟨[3, 2]⟩ : PomFiberFenceData).hasBirkhoffFenceIdealRepresentation ∧
        zigzagComponentLengthMultiset [2, 3] ≠ zigzagComponentLengthMultiset [3, 2] := by
    apply paper_pom_fiber_symmetric_order_visible_layer_separation
    · intro n hn
      simp at hn
      rcases hn with rfl | rfl <;> omega
    · intro n hn
      simp at hn
      rcases hn with rfl | rfl <;> omega
    · simp
    · decide
  exact ⟨hseparation.1, hseparation.2.2.2⟩

end Omega.POM

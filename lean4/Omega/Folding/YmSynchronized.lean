namespace Omega.Folding

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the synchronizing-symbol corollary of the
finite-state presentation.
    cor:Y-m-synchronized -/
theorem paper_resolution_folding_y_m_synchronized
    {Symbol : Type}
    (a_m b_m : Symbol)
    (labelsUniqueEdge synchronizing : Symbol → Prop)
    (rightResolvingPresentation imageLanguageSynchronized : Prop)
    (hUniqueToSync : ∀ x, labelsUniqueEdge x → synchronizing x)
    (hImage : rightResolvingPresentation ∧ (synchronizing a_m ∨ synchronizing b_m) →
      imageLanguageSynchronized)
    (hRight : rightResolvingPresentation)
    (hUniqueA : labelsUniqueEdge a_m)
    (hUniqueB : labelsUniqueEdge b_m) :
    synchronizing a_m ∧ synchronizing b_m ∧ imageLanguageSynchronized := by
  have hSyncA : synchronizing a_m := hUniqueToSync a_m hUniqueA
  have hSyncB : synchronizing b_m := hUniqueToSync b_m hUniqueB
  exact ⟨hSyncA, hSyncB, hImage ⟨hRight, Or.inl hSyncA⟩⟩

end Omega.Folding

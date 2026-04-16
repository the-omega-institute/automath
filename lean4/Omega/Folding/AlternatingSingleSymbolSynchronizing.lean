namespace Omega.Folding

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the alternating-symbol synchronization theorem
in the finite-state presentation.
    thm:alternating-single-symbol-synchronizing -/
theorem paper_resolution_folding_alternating_single_symbol_synchronizing
    {Symbol : Type}
    (a_m b_m : Symbol)
    (fiberSingleton uniqueEdgeLabel synchronizing : Symbol → Prop)
    (hFiberToUnique : ∀ x, fiberSingleton x → uniqueEdgeLabel x)
    (hUniqueToSync : ∀ x, uniqueEdgeLabel x → synchronizing x)
    (ha : fiberSingleton a_m)
    (hb : fiberSingleton b_m) :
    uniqueEdgeLabel a_m ∧
      uniqueEdgeLabel b_m ∧
      synchronizing a_m ∧
      synchronizing b_m := by
  have hUniqueA : uniqueEdgeLabel a_m := hFiberToUnique a_m ha
  have hUniqueB : uniqueEdgeLabel b_m := hFiberToUnique b_m hb
  exact ⟨hUniqueA, hUniqueB, hUniqueToSync a_m hUniqueA, hUniqueToSync b_m hUniqueB⟩

end Omega.Folding

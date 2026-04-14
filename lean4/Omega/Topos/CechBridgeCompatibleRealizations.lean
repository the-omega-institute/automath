namespace Omega.Topos

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for constructing the Cech obstruction class of a
    branch gerbe from compatible local realizations.
    thm:cech-bridge-compatible-realizations -/
theorem paper_gluing_failure_cech_bridge_compatible_realizations
    (pairwiseIsomorphisms cocycleCondition classIndependence neutral branchClassZero : Prop)
    (hIso : pairwiseIsomorphisms)
    (hCocycle : pairwiseIsomorphisms → cocycleCondition)
    (hClass : pairwiseIsomorphisms → classIndependence)
    (hNeutralToZero : pairwiseIsomorphisms → neutral → branchClassZero)
    (hZeroToNeutral : pairwiseIsomorphisms → branchClassZero → neutral) :
    pairwiseIsomorphisms ∧
      cocycleCondition ∧
      classIndependence ∧
      (branchClassZero ↔ neutral) := by
  refine ⟨hIso, hCocycle hIso, hClass hIso, ?_⟩
  constructor
  · intro hZero
    exact hZeroToNeutral hIso hZero
  · intro hNeutral
    exact hNeutralToZero hIso hNeutral

end Omega.Topos

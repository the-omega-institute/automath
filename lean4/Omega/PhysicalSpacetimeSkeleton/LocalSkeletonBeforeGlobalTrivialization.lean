import Mathlib.Tactic

namespace Omega.PhysicalSpacetimeSkeleton

set_option maxHeartbeats 400000 in
/-- Paper-facing wrapper separating local skeleton existence from the extra hypotheses needed for
    global untwisted trivialization and Einstein closure.
    prop:physical-spacetime-local-skeleton-before-global-trivialization -/
theorem paper_physical_spacetime_local_skeleton_before_global_trivialization
    {Patch Skeleton : Type*}
    (localSkeleton : Patch → Skeleton → Prop) (globalUntwistedSkeleton : Skeleton → Prop)
    (tripleObstructionTrivial cechOneCocycleTrivial einsteinClosure : Prop)
    (globalizationForcesTriviality :
      (∃ s : Skeleton, globalUntwistedSkeleton s) →
        tripleObstructionTrivial ∧ cechOneCocycleTrivial)
    (closureRequiresGlobal : einsteinClosure → ∃ s : Skeleton, globalUntwistedSkeleton s)
    (localData : ∀ i : Patch, ∃ s : Skeleton, localSkeleton i s) :
    (∀ i : Patch, ∃ s : Skeleton, localSkeleton i s) ∧
      ((∃ s : Skeleton, globalUntwistedSkeleton s) →
        tripleObstructionTrivial ∧ cechOneCocycleTrivial) ∧
      ((¬ tripleObstructionTrivial ∨ ¬ cechOneCocycleTrivial) → ¬ einsteinClosure) := by
  refine ⟨localData, globalizationForcesTriviality, ?_⟩
  intro hObstruction hEinstein
  rcases closureRequiresGlobal hEinstein with ⟨s, hs⟩
  rcases globalizationForcesTriviality ⟨s, hs⟩ with ⟨hTriple, hCech⟩
  rcases hObstruction with hTripleFalse | hCechFalse
  · exact hTripleFalse hTriple
  · exact hCechFalse hCech

end Omega.PhysicalSpacetimeSkeleton

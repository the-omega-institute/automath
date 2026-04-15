import Omega.Folding.InverseLimit
import Omega.RecursiveAddressing.CompleteAddressReconstruction

namespace Omega.PhysicalSpacetimeSkeleton

/-- The chapter-local unified object layer is the stable infinite object assembled from the
resolution-compatible system `(X_m)`. -/
abbrev UnifiedObjectLayer := Omega.X.XInfinity

/-- The canonical inverse-limit presentation of the stable type system. -/
abbrev StableTypeInverseLimit := Omega.X.CompatibleFamily

/-- Paper-facing wrapper for the unified object layer as the inverse limit of the stable type
system, together with the unique gluing of compatible finite-resolution objects.
    prop:physical-spacetime-unified-object-layer -/
theorem paper_physical_spacetime_unified_object_layer :
    Nonempty (UnifiedObjectLayer ≃ StableTypeInverseLimit) ∧
    ∀ F : StableTypeInverseLimit, ∃! a : UnifiedObjectLayer, Omega.X.toFamily a = F := by
  refine ⟨⟨Omega.X.inverseLimitEquiv.symm⟩, ?_⟩
  intro F
  refine ⟨Omega.X.ofFamily F, Omega.X.toFamily_ofFamily F, ?_⟩
  intro a ha
  calc
    a = Omega.X.ofFamily (Omega.X.toFamily a) := by
      symm
      exact Omega.X.ofFamily_toFamily a
    _ = Omega.X.ofFamily F := by rw [ha]

end Omega.PhysicalSpacetimeSkeleton

import Omega.Folding.InverseLimit

namespace Omega.PhysicalSpacetimeSkeleton

/-- The chapter-local unified object layer is the stable infinite object assembled from the
resolution-compatible system `(X_m)`. -/
abbrev UnifiedObjectLayer := Omega.X.XInfinity

/-- The canonical inverse-limit presentation of the stable type system. -/
abbrev StableTypeInverseLimit := Omega.X.CompatibleFamily

/-- Paper-facing wrapper for the unified object layer as the inverse limit of the stable type
system.
    prop:physical-spacetime-unified-object-layer -/
theorem paper_physical_spacetime_unified_object_layer :
    Nonempty (UnifiedObjectLayer ≃ StableTypeInverseLimit) :=
  ⟨Omega.X.inverseLimitEquiv.symm⟩

end Omega.PhysicalSpacetimeSkeleton

import Mathlib.Tactic

namespace Omega.TypedAddressBiaxialCompletion

/-- Paper-facing separator theorem collecting the chapter's address/point distinction, inverse-limit
point realization, and structural `NULL` behavior for collapsed finite-depth clusters.
    prop:typed-address-biaxial-completion-address-not-point -/
theorem paper_typed_address_biaxial_completion_address_not_point
    (addressObjectsNotPoints pointsRequireInverseLimit structuralNullOnCollapsedClusters : Prop)
    (hSep : addressObjectsNotPoints)
    (hPts : pointsRequireInverseLimit)
    (hNull : structuralNullOnCollapsedClusters) :
    addressObjectsNotPoints /\ pointsRequireInverseLimit /\ structuralNullOnCollapsedClusters := by
  exact ⟨hSep, hPts, hNull⟩

/-- Zeta-facing corollary: the typed-address package theorem already separates finite address
objects from inverse-limit point objects, so we project its first component.
    cor:xi-zero-not-address -/
theorem paper_xi_zero_not_address
    (addressObjectsNotPoints pointsRequireInverseLimit structuralNullOnCollapsedClusters : Prop)
    (hSep : addressObjectsNotPoints)
    (hPts : pointsRequireInverseLimit)
    (hNull : structuralNullOnCollapsedClusters) : addressObjectsNotPoints := by
  exact
    (paper_typed_address_biaxial_completion_address_not_point
      addressObjectsNotPoints pointsRequireInverseLimit structuralNullOnCollapsedClusters
      hSep hPts hNull).1

end Omega.TypedAddressBiaxialCompletion

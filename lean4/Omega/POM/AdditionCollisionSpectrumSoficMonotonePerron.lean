import Mathlib

namespace Omega.POM

/-- Paper-facing wrapper for the sofic monotonicity bound on the addition collision spectrum:
    an entrywise-bounded real-input subkernel inherits nonnegativity and spectral-radius
    monotonicity from the unconstrained sync kernel, and deleting a Perron-supported path forces
    a strict spectral drop.
    prop:add-collision-spectrum-sofic-monotone-perron -/
theorem paper_add_collision_spectrum_sofic_monotone_perron
    (entrywiseBound nonnegative spectralRadiusMonotone deletedPerronPath strictDrop : Prop)
    (hNonnegative : nonnegative)
    (hMonotone : entrywiseBound → nonnegative → spectralRadiusMonotone)
    (hStrictDrop : spectralRadiusMonotone → deletedPerronPath → strictDrop) :
    entrywiseBound →
      nonnegative ∧ spectralRadiusMonotone ∧ (deletedPerronPath → strictDrop) := by
  intro hBound
  have hRadius : spectralRadiusMonotone := hMonotone hBound hNonnegative
  exact ⟨hNonnegative, hRadius, fun hDelete => hStrictDrop hRadius hDelete⟩

end Omega.POM

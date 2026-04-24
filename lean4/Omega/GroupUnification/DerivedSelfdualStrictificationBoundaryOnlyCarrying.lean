import Mathlib.Tactic

namespace Omega.GroupUnification

/-- Concrete endpoint audit data for the boundary-only carrying conclusion under self-dual
strictification. -/
structure DerivedSelfdualStrictificationBoundaryOnlyCarryingData where
  Carrier : Type
  onBoundary : Carrier → Prop
  interiorSingular : Carrier → Prop
  phaseCurrent : Carrier → ℤ
  offsetMass : ℕ
  auditedInnerPhaseCurrentBound : ℕ
  carryingSupport :
    ∀ x, phaseCurrent x ≠ 0 → onBoundary x ∨ interiorSingular x
  interiorVanish :
    ∀ x, interiorSingular x → phaseCurrent x = 0
  endpointCertificate :
    offsetMass ≤ auditedInnerPhaseCurrentBound

namespace DerivedSelfdualStrictificationBoundaryOnlyCarryingData

/-- The interior singular current vanishes identically. -/
def noInteriorSingularity (D : DerivedSelfdualStrictificationBoundaryOnlyCarryingData) : Prop :=
  ∀ x, D.interiorSingular x → D.phaseCurrent x = 0

/-- Any surviving nonzero current is necessarily boundary-supported. -/
def boundaryOnlyCarrying (D : DerivedSelfdualStrictificationBoundaryOnlyCarryingData) : Prop :=
  ∀ x, D.phaseCurrent x ≠ 0 → D.onBoundary x

/-- The total offset mass is bounded by the audited endpoint current budget. -/
def offsetMassBound (D : DerivedSelfdualStrictificationBoundaryOnlyCarryingData) : Prop :=
  D.offsetMass ≤ D.auditedInnerPhaseCurrentBound

lemma noInteriorSingularity_of_data (D : DerivedSelfdualStrictificationBoundaryOnlyCarryingData) :
    D.noInteriorSingularity := by
  intro x hx
  exact D.interiorVanish x hx

lemma boundaryOnlyCarrying_of_data
    (D : DerivedSelfdualStrictificationBoundaryOnlyCarryingData) :
    D.boundaryOnlyCarrying := by
  intro x hx
  rcases D.carryingSupport x hx with hBoundary | hInterior
  · exact hBoundary
  · have hZero := D.interiorVanish x hInterior
    exact False.elim (hx hZero)

lemma offsetMassBound_of_data (D : DerivedSelfdualStrictificationBoundaryOnlyCarryingData) :
    D.offsetMassBound := by
  exact D.endpointCertificate

end DerivedSelfdualStrictificationBoundaryOnlyCarryingData

open DerivedSelfdualStrictificationBoundaryOnlyCarryingData

/-- Self-dual strictification kills interior singular carrying, leaves only boundary-supported
current, and bounds the total offset mass by the audited endpoint budget.
    thm:derived-selfdual-strictification-boundary-only-carrying -/
theorem paper_derived_selfdual_strictification_boundary_only_carrying
    (D : DerivedSelfdualStrictificationBoundaryOnlyCarryingData) :
    D.noInteriorSingularity ∧ D.boundaryOnlyCarrying ∧ D.offsetMassBound := by
  exact ⟨D.noInteriorSingularity_of_data, D.boundaryOnlyCarrying_of_data,
    D.offsetMassBound_of_data⟩

end Omega.GroupUnification

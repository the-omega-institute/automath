import Mathlib.Tactic
import Omega.TypedAddressBiaxialCompletion.BiaxialNonsubstitutable
import Omega.TypedAddressBiaxialCompletion.BoundaryAddressCollision

namespace Omega.TypedAddressBiaxialCompletion

open BoundaryAddressCollision
open scoped BigOperators

/-- The boundary-radius budget is witnessed by an address class that carries the average
occupancy forced by the collision lower bound. -/
def radiusScale (c T : ℝ) (b : ℕ) (addressOccupancy : Fin (2 ^ b) → ℝ) : Prop :=
  ∃ a : Fin (2 ^ b), c * T^2 * Real.log T / (2 : ℝ) ^ b ≤ addressOccupancy a

/-- The boundary-depth budget records that the visible quotient and kernel ledger axes remain
separate coordinates of the completed address object. -/
def depthScale (E : CompletePhaseExtension) : Prop :=
  phaseAxisDependsOnlyOnVisibleQuotient E ∧ ledgerAxisDependsOnlyOnKernel E

/-- Radius witnesses and depth witnesses live on different pieces of data, so the depth axis
cannot replace the radius axis. -/
def notSubstitutable (E : CompletePhaseExtension) : Prop :=
  requiresOrderedPair E

/-- `cor:typed-address-biaxial-completion-boundary-depth-not-radius`. The radius budget comes
from the boundary-collision estimate, while the depth budget and the non-substitutability claim
come from the biaxial visible/kernel axis separation. -/
theorem paper_typed_address_biaxial_completion_boundary_depth_not_radius
    (E : CompletePhaseExtension) (c T : ℝ) (b : ℕ) (addressOccupancy : Fin (2 ^ b) → ℝ)
    (hNonneg : ∀ a, 0 ≤ addressOccupancy a)
    (hTotal : c * T^2 * Real.log T ≤ ∑ a, addressOccupancy a) :
    radiusScale c T b addressOccupancy ∧ depthScale E ∧ notSubstitutable E := by
  have hRadius :
      radiusScale c T b addressOccupancy :=
    paper_typed_address_biaxial_completion_boundary_address_collision c T b addressOccupancy
      hNonneg hTotal
  rcases paper_typed_address_biaxial_completion_biaxial_nonsubstitutable E with
    ⟨hVisible, hLedger, hOrdered⟩
  exact ⟨hRadius, ⟨hVisible, hLedger⟩, hOrdered⟩

end Omega.TypedAddressBiaxialCompletion

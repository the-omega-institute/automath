import Omega.TypedAddressBiaxialCompletion.BoundaryAddressCollision

namespace Omega.UnitCirclePhaseArithmetic

open Omega.TypedAddressBiaxialCompletion.BoundaryAddressCollision
open scoped BigOperators

/-- Appendix/unit-circle wrapper of the typed-address boundary collision bound.
    prop:unit-circle-boundary-dyadic-collision -/
theorem paper_unit_circle_boundary_dyadic_collision
    (c T : ℝ) (b : ℕ) (addressOccupancy : Fin (2 ^ b) → ℝ)
    (hNonneg : ∀ a, 0 ≤ addressOccupancy a)
    (hTotal : c * T^2 * Real.log T ≤ ∑ a, addressOccupancy a) :
    ∃ a : Fin (2 ^ b), c * T^2 * Real.log T / (2 : ℝ) ^ b ≤ addressOccupancy a := by
  exact
    paper_typed_address_biaxial_completion_boundary_address_collision c T b addressOccupancy
      hNonneg hTotal

end Omega.UnitCirclePhaseArithmetic

import Mathlib.Tactic
import Omega.TypedAddressBiaxialCompletion.Window6AuditBoundaryCertificates

namespace Omega.TypedAddressBiaxialCompletion

/-- Boundary holonomy rank before quotienting by the geometric diagonal. -/
def window6BoundaryHolonomyRank : Nat :=
  window6BoundaryCenterRank

/-- Rank of the diagonal geometric subgroup. -/
def window6BoundaryGeometricDiagonalRank : Nat :=
  window6BoundaryGeometricRank

/-- Rank of the residual quotient after removing the diagonal geometric bit. -/
def window6BoundaryResidualRank : Nat :=
  window6BoundaryQuotientRank

/-- Cardinality of the residual `F₂`-vector-space quotient. -/
def window6BoundaryResidualCardinality : Nat :=
  (2 : Nat) ^ window6BoundaryResidualRank

/-- Paper-facing wrapper for the window-6 boundary holonomy package: the three involutions give a
rank-`3` boundary parity sector, the geometric diagonal contributes one bit, and the residual
quotient has rank `2`, hence cardinality `4`.
    prop:typed-address-biaxial-completion-window6-boundary-holonomy -/
theorem paper_typed_address_biaxial_completion_window6_boundary_holonomy :
    window6BoundaryHolonomyRank = 3 ∧
      window6BoundaryGeometricDiagonalRank = 1 ∧
      window6BoundaryResidualRank = 2 ∧
      window6BoundaryHolonomyRank =
        window6BoundaryGeometricDiagonalRank + window6BoundaryResidualRank ∧
      window6BoundaryResidualCardinality = 4 := by
  rcases paper_typed_address_biaxial_completion_window6_audit_boundary_certificates with
    ⟨hCenterRank, _, hGeoRank, _, hResidualRank, hResidualCard, hSum, _⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [window6BoundaryHolonomyRank] using hCenterRank
  · simpa [window6BoundaryGeometricDiagonalRank] using hGeoRank
  · simpa [window6BoundaryResidualRank] using hResidualRank
  · simpa [window6BoundaryHolonomyRank, window6BoundaryGeometricDiagonalRank,
      window6BoundaryResidualRank] using hSum
  · simpa [window6BoundaryResidualCardinality, window6BoundaryResidualRank] using hResidualCard

end Omega.TypedAddressBiaxialCompletion

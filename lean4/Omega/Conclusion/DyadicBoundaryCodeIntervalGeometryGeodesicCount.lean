import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete finite Boolean-coordinate model for squarefree boundary codes. The finite set
`differingCoordinates` is the symmetric-difference support between the two codes. The interval
consists of all Boolean choices on this support, and shortest paths are permutations of the same
coordinates. -/
structure conclusion_dyadic_boundary_code_interval_geometry_geodesic_count_data where
  Coordinate : Type
  instDecidableEqCoordinate : DecidableEq Coordinate
  instFintypeCoordinate : Fintype Coordinate
  differingCoordinates : Finset Coordinate

attribute [instance]
  conclusion_dyadic_boundary_code_interval_geometry_geodesic_count_data.instDecidableEqCoordinate
  conclusion_dyadic_boundary_code_interval_geometry_geodesic_count_data.instFintypeCoordinate

namespace conclusion_dyadic_boundary_code_interval_geometry_geodesic_count_data

/-- Arithmetic distance is the number of independent squarefree divisor coordinates on which the
two boundary codes differ. -/
def arithmeticDistance
    (D : conclusion_dyadic_boundary_code_interval_geometry_geodesic_count_data) : ℕ :=
  D.differingCoordinates.card

/-- The geodesic interval is the Boolean cube of independent divisor choices on the differing
coordinates. -/
def intervalCardinality
    (D : conclusion_dyadic_boundary_code_interval_geometry_geodesic_count_data) : ℕ :=
  Fintype.card (D.differingCoordinates → Bool)

/-- A shortest path orders each differing coordinate exactly once. -/
def shortestPathCount
    (D : conclusion_dyadic_boundary_code_interval_geometry_geodesic_count_data) : ℕ :=
  D.differingCoordinates.card.factorial

end conclusion_dyadic_boundary_code_interval_geometry_geodesic_count_data

open conclusion_dyadic_boundary_code_interval_geometry_geodesic_count_data

/-- Paper label:
`thm:conclusion-dyadic-boundary-code-interval-geometry-geodesic-count`. In the finite
Boolean-coordinate model for squarefree boundary codes, the interval is the full cube of
independent divisor choices and shortest geodesics are permutations of the differing
coordinates. -/
theorem paper_conclusion_dyadic_boundary_code_interval_geometry_geodesic_count
    (D : conclusion_dyadic_boundary_code_interval_geometry_geodesic_count_data) :
    D.intervalCardinality = 2 ^ D.arithmeticDistance ∧
      D.shortestPathCount = D.arithmeticDistance.factorial := by
  constructor
  · simp [intervalCardinality, arithmeticDistance]
  · simp [shortestPathCount, arithmeticDistance]

end Omega.Conclusion

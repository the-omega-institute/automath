import Omega.SPG.PrefixScanErrorBoundaryDimensionUpper

namespace Omega.SPG

set_option maxHeartbeats 400000 in
/-- Exact paper-facing wrapper for the finite-resolution clarity bound.
    thm:spg-clarity-boundary-dimension -/
theorem paper_spg_clarity_boundary_dimension
    [MeasurableSpace (Word n)] (μ : MeasureTheory.Measure (Word n)) (h : m ≤ n) (P : Set (Word n))
    (hP : MeasurableSet P) (κ : ENNReal)
    (hκ : ∀ a : Word m, cellMeasure μ (prefixObservation h) a ≤ κ) :
    prefixScanErrorMeasure μ h P ≤ (prefixBoundaryCylinderCount μ h P : ENNReal) * (κ / 2) := by
  simpa using paper_scan_projection_address_clarity_boundary_dimension_seeds μ h P hP κ hκ

end Omega.SPG

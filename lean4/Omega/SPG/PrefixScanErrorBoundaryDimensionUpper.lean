import Omega.SPG.BoundaryDimensionUpper

namespace Omega.SPG

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the prefix scan-error boundary-dimension theorem. The Lean core
    supplies the finite-resolution upper bound; the asymptotic decay clause is carried as an
    explicit publication-facing hypothesis.
    thm:boundary-dimension -/
theorem paper_prefix_scan_error_boundary_dimension_upper
    [MeasurableSpace (Word n)] (μ : MeasureTheory.Measure (Word n))
    (h : m ≤ n) (P : Set (Word n)) (hP : MeasurableSet P) (κ : ENNReal)
    (hκ : ∀ a : Word m, cellMeasure μ (prefixObservation h) a ≤ κ)
    (dimensionDecay : Prop) (hDecay : dimensionDecay) :
    prefixScanErrorMeasure μ h P ≤ (prefixBoundaryCylinderCount μ h P : ENNReal) * (κ / 2) ∧
      dimensionDecay := by
  exact
    ⟨paper_scan_projection_address_clarity_boundary_dimension_seeds μ h P hP κ hκ, hDecay⟩

end Omega.SPG

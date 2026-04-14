import Omega.SPG.WeightedBoundaryDecomposition

open scoped BigOperators

namespace Omega.SPG

set_option maxHeartbeats 400000 in
/-- Paper-facing seed for the upper boundary estimate in the clarity section:
    if every depth-`m` cylinder has mass at most `κ`, then the scan error is
    bounded by `κ / 2` times the number of boundary cylinders.
    thm:clarity-boundary-dimension -/
theorem paper_scan_projection_address_clarity_boundary_dimension_seeds
    [MeasurableSpace (Word n)] (μ : MeasureTheory.Measure (Word n))
    (h : m ≤ n) (P : Set (Word n)) (hP : MeasurableSet P) (κ : ENNReal)
    (hκ : ∀ a : Word m, cellMeasure μ (prefixObservation h) a ≤ κ) :
    prefixScanErrorMeasure μ h P ≤ (prefixBoundaryCylinderCount μ h P : ENNReal) * (κ / 2) := by
  have hbd :=
    (paper_scan_projection_address_weighted_boundary_decomposition_seeds μ h P hP).2
  refine hbd.trans ?_
  calc
    Finset.sum (prefixBoundaryCellsMeasure μ h P) (fun a => cellMeasure μ (prefixObservation h) a / 2)
      ≤ Finset.sum (prefixBoundaryCellsMeasure μ h P) (fun _ => κ / 2) := by
        refine Finset.sum_le_sum ?_
        intro a ha
        simpa [div_eq_mul_inv] using mul_le_mul_left (hκ a) ((2 : ENNReal)⁻¹)
    _ = (prefixBoundaryCylinderCount μ h P : ENNReal) * (κ / 2) := by
        simp [prefixBoundaryCylinderCount, mul_comm]

end Omega.SPG

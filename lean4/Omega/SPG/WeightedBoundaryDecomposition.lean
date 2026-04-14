import Omega.SPG.ScanErrorMeasure

open scoped BigOperators

namespace Omega.SPG

private theorem min_le_half_sum (a b : ENNReal) : min a b ≤ (a + b) / 2 := by
  have htwo_ne_zero : (2 : ENNReal) ≠ 0 := by norm_num
  have htwo_ne_top : (2 : ENNReal) ≠ ⊤ := by simp
  refine (ENNReal.le_div_iff_mul_le (Or.inl htwo_ne_zero) (Or.inl htwo_ne_top)).2 ?_
  simpa [mul_comm, mul_left_comm, mul_assoc, two_mul, mul_two] using
    add_le_add (min_le_left a b) (min_le_right a b)

private theorem boundary_term_le_half_cell [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) (obs : α → β) (P : Set α) (b : β) (hP : MeasurableSet P) :
    min (cellEventMeasure μ obs P b) (cellComplMeasure μ obs P b) ≤ cellMeasure μ obs b / 2 := by
  calc
    min (cellEventMeasure μ obs P b) (cellComplMeasure μ obs P b) ≤
        (cellEventMeasure μ obs P b + cellComplMeasure μ obs P b) / 2 :=
      min_le_half_sum _ _
    _ = cellMeasure μ obs b / 2 := by
      rw [cellEventMeasure_add_cellComplMeasure_eq_cellMeasure μ obs P b hP]

set_option maxHeartbeats 400000 in
/-- Paper-facing seed for the weighted boundary decomposition in the clarity section:
    the scan error localizes to boundary cylinders, and each boundary contribution
    is bounded by half of the corresponding cylinder mass.
    prop:weighted-boundary-decomposition -/
theorem paper_scan_projection_address_weighted_boundary_decomposition_seeds
    [MeasurableSpace (Word n)] (μ : MeasureTheory.Measure (Word n))
    (h : m ≤ n) (P : Set (Word n)) (hP : MeasurableSet P) :
    prefixScanErrorMeasure μ h P =
      Finset.sum (prefixBoundaryCellsMeasure μ h P) (fun a =>
        min (cellEventMeasure μ (prefixObservation h) P a)
          (cellComplMeasure μ (prefixObservation h) P a)) ∧
    prefixScanErrorMeasure μ h P ≤
      Finset.sum (prefixBoundaryCellsMeasure μ h P) (fun a =>
        cellMeasure μ (prefixObservation h) a / 2) := by
  refine ⟨prefixScanErrorMeasure_eq_sum_boundary μ h P, ?_⟩
  rw [prefixScanErrorMeasure_eq_sum_boundary]
  refine Finset.sum_le_sum ?_
  intro a ha
  exact boundary_term_le_half_cell μ (prefixObservation h) P a hP

end Omega.SPG

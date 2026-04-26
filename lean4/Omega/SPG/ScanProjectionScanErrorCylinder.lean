import Omega.SPG.ScanErrorDiscrete

namespace Omega.SPG.ScanProjectionScanErrorCylinder

/-- Paper-facing seeds for `prop:scan-error-cylinder`.
    For the prefix observable, the scan error is exactly the cellwise Bayes minimum sum,
    equivalently the same sum restricted to the non-pure boundary cells. -/
theorem paper_scan_projection_address_scan_error_cylinder_seeds
    (μ : PMF (Word n)) (h : m ≤ n) (P : Set (Word n)) :
    (prefixScanError μ h P =
      Finset.sum Finset.univ (fun a : Word m =>
        min (cellEventMass μ (prefixObservation h) P a)
          (cellComplMass μ (prefixObservation h) P a))) ∧
    (prefixScanError μ h P =
      Finset.sum (prefixBoundaryCells μ h P) (fun a =>
        min (cellEventMass μ (prefixObservation h) P a)
          (cellComplMass μ (prefixObservation h) P a))) := by
  constructor
  · rfl
  · exact prefixScanError_eq_sum_boundary μ h P

/-- Packaged form of the `prop:scan-error-cylinder` seeds. -/
theorem paper_scan_projection_address_scan_error_cylinder_package
    (μ : PMF (Word n)) (h : m ≤ n) (P : Set (Word n)) :
    (prefixScanError μ h P =
      Finset.sum Finset.univ (fun a : Word m =>
        min (cellEventMass μ (prefixObservation h) P a)
          (cellComplMass μ (prefixObservation h) P a))) ∧
    (prefixScanError μ h P =
      Finset.sum (prefixBoundaryCells μ h P) (fun a =>
        min (cellEventMass μ (prefixObservation h) P a)
          (cellComplMass μ (prefixObservation h) P a))) :=
  paper_scan_projection_address_scan_error_cylinder_seeds μ h P

/-- Paper-facing package for `prop:spg-scan-error-cylinder`. -/
theorem paper_spg_scan_error_cylinder
    (μ : PMF (Word n)) (h : m ≤ n) (P : Set (Word n)) :
    (prefixScanError μ h P =
      Finset.sum Finset.univ (fun a : Word m =>
        min (cellEventMass μ (prefixObservation h) P a)
          (cellComplMass μ (prefixObservation h) P a))) ∧
    (prefixScanError μ h P =
      Finset.sum (prefixBoundaryCells μ h P) (fun a =>
        min (cellEventMass μ (prefixObservation h) P a)
          (cellComplMass μ (prefixObservation h) P a))) :=
  paper_scan_projection_address_scan_error_cylinder_package μ h P

end Omega.SPG.ScanProjectionScanErrorCylinder

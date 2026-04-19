import Mathlib.Tactic
import Mathlib.Analysis.SpecificLimits.Normed

namespace Omega.Multiscale

open Filter Topology

/-- Chapter-local data for the robust normalized Stokes identity with defect budget. The package
records the normalized bulk, boundary, and defect sequences together with their limiting values,
the layerwise Stokes identity, and the a priori defect budget controlling the limiting error. -/
structure RobustNormalizedStokesWithDefectBudgetData where
  normalizedBulk : ℕ → ℝ
  normalizedBoundary : ℕ → ℝ
  normalizedDefect : ℕ → ℝ
  bulkLimit : ℝ
  boundaryLimit : ℝ
  defectLimit : ℝ
  defectBudget : ℝ
  layerwiseStokes :
    ∀ n, normalizedBulk n - normalizedBoundary n = normalizedDefect n
  bulk_tendsto :
    Tendsto normalizedBulk atTop (𝓝 bulkLimit)
  boundary_tendsto :
    Tendsto normalizedBoundary atTop (𝓝 boundaryLimit)
  defect_tendsto :
    Tendsto normalizedDefect atTop (𝓝 defectLimit)
  defectLimit_abs_le_budget :
    |defectLimit| ≤ defectBudget

/-- Paper-facing robust normalized Stokes identity with defect budget: the layerwise identities
pass to the limit, and the limiting defect is controlled by the prescribed budget.
    cor:app-robust-normalized-stokes-with-defect-budget -/
theorem paper_app_robust_normalized_stokes_with_defect_budget
    (D : RobustNormalizedStokesWithDefectBudgetData) :
    D.bulkLimit - D.boundaryLimit = D.defectLimit ∧
      |D.bulkLimit - D.boundaryLimit| ≤ D.defectBudget := by
  have hSub :
      Tendsto (fun n => D.normalizedBulk n - D.normalizedBoundary n) atTop
        (𝓝 (D.bulkLimit - D.boundaryLimit)) :=
    D.bulk_tendsto.sub D.boundary_tendsto
  have hDefect :
      Tendsto (fun n => D.normalizedBulk n - D.normalizedBoundary n) atTop (𝓝 D.defectLimit) := by
    simpa [funext D.layerwiseStokes] using D.defect_tendsto
  have hId : D.bulkLimit - D.boundaryLimit = D.defectLimit :=
    tendsto_nhds_unique hSub hDefect
  exact ⟨hId, by simpa [hId] using D.defectLimit_abs_le_budget⟩

end Omega.Multiscale

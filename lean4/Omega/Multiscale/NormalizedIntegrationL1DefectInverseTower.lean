import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

namespace Omega.Multiscale

open Filter Topology

/-- Concrete data for a normalized inverse tower with `ℓ¹` defect control. The three sequences are
the normalized bulk, boundary, and defect terms; their tail budgets quantify convergence to the
proposed limiting values. -/
structure NormalizedIntegrationL1DefectInverseTowerData where
  normalizedBulk : ℕ → ℝ
  normalizedBoundary : ℕ → ℝ
  normalizedDefect : ℕ → ℝ
  bulkLimit : ℝ
  boundaryLimit : ℝ
  defectLimit : ℝ
  bulkTailBound : ℕ → ℝ
  boundaryTailBound : ℕ → ℝ
  defectTailBound : ℕ → ℝ
  layerwiseStokes :
    ∀ n, normalizedBulk n - normalizedBoundary n = normalizedDefect n
  bulk_tail :
    ∀ n, |bulkLimit - normalizedBulk n| ≤ bulkTailBound n
  boundary_tail :
    ∀ n, |boundaryLimit - normalizedBoundary n| ≤ boundaryTailBound n
  defect_tail :
    ∀ n, |defectLimit - normalizedDefect n| ≤ defectTailBound n
  bulkTail_tendsto_zero :
    Tendsto bulkTailBound atTop (𝓝 0)
  boundaryTail_tendsto_zero :
    Tendsto boundaryTailBound atTop (𝓝 0)
  defectTail_tendsto_zero :
    Tendsto defectTailBound atTop (𝓝 0)

/-- The limiting Stokes identity for the normalized inverse tower. -/
def NormalizedIntegrationL1DefectInverseTowerData.limitStokes
    (D : NormalizedIntegrationL1DefectInverseTowerData) : Prop :=
  D.bulkLimit - D.boundaryLimit = D.defectLimit

private theorem tendsto_of_abs_sub_le
    {u : ℕ → ℝ} {L : ℝ} {b : ℕ → ℝ}
    (hBound : ∀ n, |L - u n| ≤ b n)
    (hTail : Tendsto b atTop (𝓝 0)) :
    Tendsto u atTop (𝓝 L) := by
  have hNorm :
      Tendsto (fun n => ‖u n - L‖) atTop (𝓝 0) := by
    have hAbs :
        Tendsto (fun n => |L - u n|) atTop (𝓝 0) :=
      squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) (Eventually.of_forall hBound)
        hTail
    simpa [Real.norm_eq_abs, abs_sub_comm] using hAbs
  exact tendsto_iff_norm_sub_tendsto_zero.2 hNorm

/-- Paper-facing normalized integration theorem: the bulk and boundary sequences converge with the
stated tail budgets, and the layerwise Stokes identity passes to the limit.
    thm:app-normalized-integration-l1-defect-inverse-tower -/
theorem paper_app_normalized_integration_l1_defect_inverse_tower
    (D : NormalizedIntegrationL1DefectInverseTowerData) :
    Tendsto D.normalizedBulk atTop (𝓝 D.bulkLimit) ∧
      (∀ N, |D.bulkLimit - D.normalizedBulk N| ≤ D.bulkTailBound N) ∧
      Tendsto D.normalizedBoundary atTop (𝓝 D.boundaryLimit) ∧ D.limitStokes := by
  have hBulk :
      Tendsto D.normalizedBulk atTop (𝓝 D.bulkLimit) :=
    tendsto_of_abs_sub_le D.bulk_tail D.bulkTail_tendsto_zero
  have hBoundary :
      Tendsto D.normalizedBoundary atTop (𝓝 D.boundaryLimit) :=
    tendsto_of_abs_sub_le D.boundary_tail D.boundaryTail_tendsto_zero
  have hDefect :
      Tendsto D.normalizedDefect atTop (𝓝 D.defectLimit) :=
    tendsto_of_abs_sub_le D.defect_tail D.defectTail_tendsto_zero
  have hSub :
      Tendsto (fun n => D.normalizedBulk n - D.normalizedBoundary n) atTop
        (𝓝 (D.bulkLimit - D.boundaryLimit)) :=
    hBulk.sub hBoundary
  have hDefectEq :
      Tendsto (fun n => D.normalizedBulk n - D.normalizedBoundary n) atTop (𝓝 D.defectLimit) :=
    by
      simpa [funext D.layerwiseStokes] using hDefect
  have hLimitStokes : D.limitStokes :=
    tendsto_nhds_unique hSub hDefectEq
  exact ⟨hBulk, D.bulk_tail, hBoundary, hLimitStokes⟩

end Omega.Multiscale

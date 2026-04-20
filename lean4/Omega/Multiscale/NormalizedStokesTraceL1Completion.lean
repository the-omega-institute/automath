import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic
import Omega.Multiscale.NormalizedIntegrationL1DefectInverseTower

namespace Omega.Multiscale

open Filter Topology

/-- Concrete data for completing the normalized Stokes trace from eventually compatible inverse
towers. The normalized bulk, boundary, and defect sequences come with `ℓ¹` tail control as in the
basic inverse-tower theorem; eventual compatibility is encoded by eventual constancy of the
boundary sequence, and the extension is recorded by a trace functional that only depends on the
eventual tail. -/
structure NormalizedStokesTraceL1CompletionData where
  normalizedBulk : ℕ → ℝ
  normalizedBoundary : ℕ → ℝ
  normalizedDefect : ℕ → ℝ
  bulkLimit : ℝ
  boundaryLimit : ℝ
  defectLimit : ℝ
  bulkTailBound : ℕ → ℝ
  boundaryTailBound : ℕ → ℝ
  defectTailBound : ℕ → ℝ
  stableIndex : ℕ
  stableValue : ℝ
  extensionValue : ℝ
  traceFunctional : (ℕ → ℝ) → ℝ
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
  boundary_eventually_stable :
    ∀ n, stableIndex ≤ n → normalizedBoundary n = stableValue
  trace_respects_tail :
    ∀ u v : ℕ → ℝ, (∃ N, ∀ n, N ≤ n → u n = v n) → traceFunctional u = traceFunctional v
  trace_on_constant :
    ∀ c : ℝ, traceFunctional (fun _ => c) = c
  trace_on_boundary :
    traceFunctional normalizedBoundary = extensionValue

namespace NormalizedStokesTraceL1CompletionData

def toNormalizedIntegrationData (D : NormalizedStokesTraceL1CompletionData) :
    NormalizedIntegrationL1DefectInverseTowerData where
  normalizedBulk := D.normalizedBulk
  normalizedBoundary := D.normalizedBoundary
  normalizedDefect := D.normalizedDefect
  bulkLimit := D.bulkLimit
  boundaryLimit := D.boundaryLimit
  defectLimit := D.defectLimit
  bulkTailBound := D.bulkTailBound
  boundaryTailBound := D.boundaryTailBound
  defectTailBound := D.defectTailBound
  layerwiseStokes := D.layerwiseStokes
  bulk_tail := D.bulk_tail
  boundary_tail := D.boundary_tail
  defect_tail := D.defect_tail
  bulkTail_tendsto_zero := D.bulkTail_tendsto_zero
  boundaryTail_tendsto_zero := D.boundaryTail_tendsto_zero
  defectTail_tendsto_zero := D.defectTail_tendsto_zero

/-- On eventually compatible towers, the limiting boundary value agrees with the stable tail
value. -/
def eventuallyCompatibleAgrees (D : NormalizedStokesTraceL1CompletionData) : Prop :=
  D.boundaryLimit = D.stableValue

/-- The normalized Stokes identity passes to the boundary limit. -/
def boundaryStokesLimit (D : NormalizedStokesTraceL1CompletionData) : Prop :=
  D.bulkLimit - D.boundaryLimit = D.defectLimit

/-- The tail-invariant trace functional extends the eventually compatible tower by the same value
as the limiting boundary trace. -/
def uniqueContinuousExtension (D : NormalizedStokesTraceL1CompletionData) : Prop :=
  D.extensionValue = D.boundaryLimit

end NormalizedStokesTraceL1CompletionData

open NormalizedStokesTraceL1CompletionData

/-- The normalized Stokes trace admits the expected `L¹` completion: eventually compatible towers
stabilize to the limiting boundary value, the normalized Stokes identity survives in the limit,
and any tail-invariant extension agrees with that same value.
    prop:app-normalized-stokes-trace-l1-completion -/
theorem paper_app_normalized_stokes_trace_l1_completion
    (D : NormalizedStokesTraceL1CompletionData) :
    D.eventuallyCompatibleAgrees ∧ D.boundaryStokesLimit ∧ D.uniqueContinuousExtension := by
  rcases paper_app_normalized_integration_l1_defect_inverse_tower D.toNormalizedIntegrationData with
    ⟨_, _, hBoundary, hLimitStokes⟩
  have hStable :
      Tendsto D.normalizedBoundary atTop (𝓝 D.stableValue) :=
    tendsto_atTop_of_eventually_const D.boundary_eventually_stable
  have hAgree : D.eventuallyCompatibleAgrees := by
    simpa [NormalizedStokesTraceL1CompletionData.eventuallyCompatibleAgrees] using
      tendsto_nhds_unique hBoundary hStable
  have hExtensionStable : D.extensionValue = D.stableValue := by
    have hTailEq :
        D.traceFunctional D.normalizedBoundary = D.traceFunctional (fun _ => D.stableValue) := by
      refine D.trace_respects_tail D.normalizedBoundary (fun _ => D.stableValue) ?_
      exact ⟨D.stableIndex, fun n hn => D.boundary_eventually_stable n hn⟩
    calc
      D.extensionValue = D.traceFunctional D.normalizedBoundary := by
        symm
        exact D.trace_on_boundary
      _ = D.traceFunctional (fun _ => D.stableValue) := hTailEq
      _ = D.stableValue := D.trace_on_constant D.stableValue
  have hBoundaryLimit : D.boundaryStokesLimit := by
    simpa [NormalizedStokesTraceL1CompletionData.boundaryStokesLimit,
      NormalizedStokesTraceL1CompletionData.toNormalizedIntegrationData,
      NormalizedIntegrationL1DefectInverseTowerData.limitStokes] using hLimitStokes
  have hUnique : D.uniqueContinuousExtension := by
    unfold NormalizedStokesTraceL1CompletionData.uniqueContinuousExtension
    rw [hExtensionStable, hAgree]
  exact ⟨hAgree, hBoundaryLimit, hUnique⟩

end Omega.Multiscale

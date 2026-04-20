import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic
import Omega.Multiscale.NormalizedStokesFiniteCoverInverseTower
import Omega.Multiscale.NormalizedStokesTraceL1Completion
import Omega.Multiscale.SolenoidStokesRadonMeasureRealization

namespace Omega.Multiscale

open Filter Topology
open NormalizedStokesFiniteCoverInverseTowerSystem

/-- Concrete data for the normalized-trace realization on a circle covering tower. The
finite-cover tower provides the levelwise Stokes identity, the normalized-trace package supplies
the limiting trace, and the Radon-measure package realizes that trace as a solenoidal measure. -/
structure SolenoidLeafwiseStokesNormalizedTraceData where
  coverSystem : NormalizedStokesFiniteCoverInverseTowerSystem
  traceData : NormalizedStokesTraceL1CompletionData
  radonData : SolenoidStokesRadonMeasureData
  baseLevel : radonData.Level
  traceDefect_eq_normalizedDifferential :
    traceData.normalizedDefect = normalizedDifferential coverSystem
  circleBoundaryEmpty : ∀ n, coverSystem.boundaryIntegral n = 0
  normalizedTrace_mass_one : traceData.extensionValue = 1
  realizedBaseMass_eq_boundaryLimit :
    radonData.inverseLimitCylinderMass baseLevel = traceData.boundaryLimit

namespace SolenoidLeafwiseStokesNormalizedTraceData

/-- The normalized trace is realized by a Radon probability measure on the inverse-limit solenoid.
-/
def normalizedTraceRealized (D : SolenoidLeafwiseStokesNormalizedTraceData) : Prop :=
  D.radonData.compatiblePushforwards ∧
    D.radonData.l1ExtensionOfStokesFunctional ∧
    D.radonData.inverseLimitCylinderMass D.baseLevel = 1

/-- The leafwise Stokes functional vanishes on the circle tower because every finite level has
empty boundary. -/
def leafwiseStokesVanishes (D : SolenoidLeafwiseStokesNormalizedTraceData) : Prop :=
  D.traceData.defectLimit = 0

end SolenoidLeafwiseStokesNormalizedTraceData

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

open SolenoidLeafwiseStokesNormalizedTraceData

/-- The normalized trace on the circle covering tower is realized by a Radon probability measure,
and the leafwise Stokes functional vanishes because the finite-level circle boundaries are empty.
    cor:app-solenoid-leafwise-stokes-normalized-trace -/
theorem paper_app_solenoid_leafwise_stokes_normalized_trace
    (D : SolenoidLeafwiseStokesNormalizedTraceData) :
    D.normalizedTraceRealized ∧ D.leafwiseStokesVanishes := by
  rcases paper_app_solenoid_stokes_radon_measure_realization D.radonData with
    ⟨hPush, _, hL1⟩
  rcases paper_app_normalized_stokes_trace_l1_completion D.traceData with ⟨_, _, hUnique⟩
  have hMass : D.radonData.inverseLimitCylinderMass D.baseLevel = 1 := by
    unfold NormalizedStokesTraceL1CompletionData.uniqueContinuousExtension at hUnique
    calc
      D.radonData.inverseLimitCylinderMass D.baseLevel = D.traceData.boundaryLimit :=
        D.realizedBaseMass_eq_boundaryLimit
      _ = D.traceData.extensionValue := by symm; exact hUnique
      _ = 1 := D.normalizedTrace_mass_one
  have hDiffBoundary :
      ∀ n,
        normalizedDifferential D.coverSystem n = normalizedBoundary D.coverSystem n := by
    rcases paper_app_normalized_stokes_finite_cover_inverse_tower D.coverSystem with
      ⟨_, _, _, hLevelwise⟩
    exact hLevelwise
  have hBoundaryZero : ∀ n, normalizedBoundary D.coverSystem n = 0 := by
    intro n
    rw [normalizedBoundary, D.circleBoundaryEmpty n]
    simp
  have hDifferentialZero : ∀ n, normalizedDifferential D.coverSystem n = 0 := by
    intro n
    rw [hDiffBoundary n, hBoundaryZero n]
  have hTraceDefectZero : ∀ n, D.traceData.normalizedDefect n = 0 := by
    intro n
    rw [D.traceDefect_eq_normalizedDifferential]
    exact hDifferentialZero n
  have hTraceDefectTendsto :
      Tendsto D.traceData.normalizedDefect atTop (𝓝 D.traceData.defectLimit) :=
    tendsto_of_abs_sub_le D.traceData.defect_tail D.traceData.defectTail_tendsto_zero
  have hZeroTendsto : Tendsto D.traceData.normalizedDefect atTop (𝓝 0) := by
    have hZeroFun : D.traceData.normalizedDefect = fun _ => (0 : ℝ) := by
      funext n
      exact hTraceDefectZero n
    rw [hZeroFun]
    exact tendsto_const_nhds
  have hLeafwise : D.traceData.defectLimit = 0 :=
    tendsto_nhds_unique hTraceDefectTendsto hZeroTendsto
  exact ⟨⟨hPush, hL1, hMass⟩, hLeafwise⟩

end Omega.Multiscale

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

open scoped BigOperators
open Filter

namespace Omega.UnitCirclePhaseArithmetic

noncomputable section

/-- The endpoint heat-kernel profile attached to a boundary point `ξ`. -/
def unitCircleBoundaryEndpointKernelBase (ξ : ℂ) : ℝ :=
  ‖((1 : ℂ) - ξ) / 2‖

/-- The `N`th endpoint heat-kernel moment. -/
def unitCircleBoundaryEndpointKernel (ξ : ℂ) (N : ℕ) : ℝ :=
  unitCircleBoundaryEndpointKernelBase ξ ^ (2 * N)

/-- A finite-support endpoint heat sequence split into the endpoint atom and the residual tail. -/
def unitCircleBoundaryEndpointHeat
    (endpointAtomMass : ℝ) (K : Finset ℂ) (μ : ℂ → ℝ) (N : ℕ) : ℝ :=
  endpointAtomMass + Finset.sum K (fun ξ => μ ξ * unitCircleBoundaryEndpointKernel ξ N)

/-- Paper label: `prop:unit-circle-boundary-endpoint-heat-decay`.
For a finite tail `K`, if the kernel base `|(1 - ξ)/2|` is uniformly bounded by `q < 1` on `K`,
then the endpoint heat sequence is antitone, converges to the endpoint atom mass, and the tail
error decays at the exponential rate `q^(2N)`. -/
theorem paper_unit_circle_boundary_endpoint_heat_decay
    (endpointAtomMass q : ℝ) (K : Finset ℂ) (μ : ℂ → ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hμ : ∀ ξ ∈ K, 0 ≤ μ ξ)
    (hkernel : ∀ ξ ∈ K, unitCircleBoundaryEndpointKernelBase ξ ≤ q) :
    Antitone (unitCircleBoundaryEndpointHeat endpointAtomMass K μ) ∧
      Tendsto (unitCircleBoundaryEndpointHeat endpointAtomMass K μ) atTop
        (nhds endpointAtomMass) ∧
      ∀ N : ℕ,
        0 ≤ unitCircleBoundaryEndpointHeat endpointAtomMass K μ N - endpointAtomMass ∧
          unitCircleBoundaryEndpointHeat endpointAtomMass K μ N - endpointAtomMass ≤
            q ^ (2 * N) * Finset.sum K (fun ξ => μ ξ) := by
  let tailMass : ℝ := Finset.sum K (fun ξ => μ ξ)
  have hq_le_one : q ≤ 1 := le_of_lt hq1
  have htail_nonneg : 0 ≤ tailMass := by
    unfold tailMass
    exact Finset.sum_nonneg (by
      intro ξ hξ
      exact hμ ξ hξ)
  have herror :
      ∀ N : ℕ,
        unitCircleBoundaryEndpointHeat endpointAtomMass K μ N - endpointAtomMass =
          Finset.sum K (fun ξ => μ ξ * unitCircleBoundaryEndpointKernel ξ N) := by
    intro N
    simp [unitCircleBoundaryEndpointHeat]
  have hbounds :
      ∀ N : ℕ,
        0 ≤ unitCircleBoundaryEndpointHeat endpointAtomMass K μ N - endpointAtomMass ∧
          unitCircleBoundaryEndpointHeat endpointAtomMass K μ N - endpointAtomMass ≤
            q ^ (2 * N) * tailMass := by
    intro N
    rw [herror]
    constructor
    · refine Finset.sum_nonneg ?_
      intro ξ hξ
      have hμ_nonneg : 0 ≤ μ ξ := hμ ξ hξ
      have hkernel_nonneg : 0 ≤ unitCircleBoundaryEndpointKernel ξ N := by
        unfold unitCircleBoundaryEndpointKernel
        exact pow_nonneg (norm_nonneg _) _
      exact mul_nonneg hμ_nonneg hkernel_nonneg
    · have hsum_le :
          Finset.sum K (fun ξ => μ ξ * unitCircleBoundaryEndpointKernel ξ N) ≤
            Finset.sum K (fun ξ => μ ξ * q ^ (2 * N)) := by
        refine Finset.sum_le_sum ?_
        intro ξ hξ
        have hμ_nonneg : 0 ≤ μ ξ := hμ ξ hξ
        have hpow_le :
            unitCircleBoundaryEndpointKernel ξ N ≤ q ^ (2 * N) := by
          unfold unitCircleBoundaryEndpointKernel
          exact pow_le_pow_left₀ (norm_nonneg _) (hkernel ξ hξ) _
        exact mul_le_mul_of_nonneg_left hpow_le hμ_nonneg
      refine hsum_le.trans ?_
      simp [tailMass, Finset.sum_mul, mul_comm]
  have hanti : Antitone (unitCircleBoundaryEndpointHeat endpointAtomMass K μ) := by
    intro m n hmn
    have hsum :
        Finset.sum K (fun ξ => μ ξ * unitCircleBoundaryEndpointKernel ξ n) ≤
          Finset.sum K (fun ξ => μ ξ * unitCircleBoundaryEndpointKernel ξ m) := by
      refine Finset.sum_le_sum ?_
      intro ξ hξ
      have hμ_nonneg : 0 ≤ μ ξ := hμ ξ hξ
      have hbase_nonneg : 0 ≤ unitCircleBoundaryEndpointKernelBase ξ := by
        exact norm_nonneg _
      have hbase_le_one : unitCircleBoundaryEndpointKernelBase ξ ≤ 1 := by
        exact (hkernel ξ hξ).trans hq_le_one
      have hkernel_le :
          unitCircleBoundaryEndpointKernel ξ n ≤ unitCircleBoundaryEndpointKernel ξ m := by
        unfold unitCircleBoundaryEndpointKernel
        exact pow_le_pow_of_le_one hbase_nonneg hbase_le_one (by omega : 2 * m ≤ 2 * n)
      exact mul_le_mul_of_nonneg_left hkernel_le hμ_nonneg
    simpa [unitCircleBoundaryEndpointHeat, add_comm, add_left_comm, add_assoc] using
      add_le_add_left hsum endpointAtomMass
  have hpow_zero :
      Tendsto (fun N : ℕ => q ^ (2 * N)) atTop (nhds 0) := by
    have hq2_nonneg : 0 ≤ q ^ 2 := by positivity
    have hq2_lt : q ^ 2 < 1 := by nlinarith
    have hpow_zero' :
        Tendsto (fun N : ℕ => (q ^ 2) ^ N) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hq2_nonneg hq2_lt
    have hpow_eq : (fun N : ℕ => q ^ (2 * N)) = fun N : ℕ => (q ^ 2) ^ N := by
      funext N
      rw [pow_mul]
    rw [hpow_eq]
    exact hpow_zero'
  have hupper_zero :
      Tendsto (fun N : ℕ => q ^ (2 * N) * tailMass) atTop (nhds 0) := by
    simpa [zero_mul] using hpow_zero.mul tendsto_const_nhds
  have herror_zero :
      Tendsto
        (fun N : ℕ => unitCircleBoundaryEndpointHeat endpointAtomMass K μ N - endpointAtomMass)
        atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper_zero
      (fun N => (hbounds N).1) ?_
    intro N
    exact (hbounds N).2
  have hlimit :
      Tendsto (unitCircleBoundaryEndpointHeat endpointAtomMass K μ) atTop
        (nhds endpointAtomMass) := by
    simpa [unitCircleBoundaryEndpointHeat, add_assoc, add_left_comm, add_comm] using
      (tendsto_const_nhds.add herror_zero)
  refine ⟨hanti, hlimit, ?_⟩
  intro N
  simpa [tailMass] using hbounds N

end

end Omega.UnitCirclePhaseArithmetic

import Omega.SPG.ScanErrorDiscrete

namespace Omega.SPG

set_option maxHeartbeats 400000 in
/-- Publication-facing finite-volume boundary scaling wrapper for the prefix scan-error paper.
    thm:volume-boundary-scaling -/
theorem paper_prefix_scan_error_volume_boundary_scaling
    {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) (θ κ_lower κ_upper : ENNReal)
    (hθ : ∀ b ∈ boundaryCells μ obs P,
      θ * cellMass μ obs b ≤ min (cellEventMass μ obs P b) (cellComplMass μ obs P b))
    (hκ_lower : ∀ b ∈ boundaryCells μ obs P, κ_lower ≤ cellMass μ obs b)
    (hκ_upper : ∀ b, cellMass μ obs b ≤ κ_upper) :
    (boundaryCells μ obs P).card * (θ * κ_lower) ≤ scanError μ obs P ∧
      scanError μ obs P ≤ (boundaryCells μ obs P).card * κ_upper := by
  refine ⟨scanError_ge_boundaryCard_mul_lower μ obs P θ κ_lower hθ hκ_lower, ?_⟩
  exact scanError_le_boundaryCard_mul μ obs P κ_upper hκ_upper

/-- Canonical paper wrapper for finite-volume boundary scaling.
    thm:spg-clarity-volume-boundary-scaling -/
theorem paper_spg_clarity_volume_boundary_scaling
    {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (P : Set α) (θ κ_lower κ_upper : ENNReal)
    (hθ : ∀ b ∈ boundaryCells μ obs P,
      θ * cellMass μ obs b ≤ min (cellEventMass μ obs P b) (cellComplMass μ obs P b))
    (hκ_lower : ∀ b ∈ boundaryCells μ obs P, κ_lower ≤ cellMass μ obs b)
    (hκ_upper : ∀ b, cellMass μ obs b ≤ κ_upper) :
    (boundaryCells μ obs P).card * (θ * κ_lower) ≤ scanError μ obs P ∧
      scanError μ obs P ≤ (boundaryCells μ obs P).card * κ_upper := by
  exact paper_prefix_scan_error_volume_boundary_scaling μ obs P θ κ_lower κ_upper
    hθ hκ_lower hκ_upper

end Omega.SPG

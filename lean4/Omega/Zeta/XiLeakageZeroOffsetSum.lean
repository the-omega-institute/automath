import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Weighted right-half-plane zero-offset sum. -/
noncomputable def xi_leakage_zero_offset_sum_zero_offset_sum
    {Zero : Type} [Fintype Zero] (halfPlaneOffset : Zero → ℝ) : ℝ :=
  ∑ ρ, halfPlaneOffset ρ

/-- Boundary leakage integral. -/
def xi_leakage_zero_offset_sum_boundary_leakage (boundaryLeakage : ℝ) : ℝ :=
  boundaryLeakage

/-- Paper label: `prop:xi-leakage-zero-offset-sum`. -/
theorem paper_xi_leakage_zero_offset_sum {Zero : Type} [Fintype Zero]
    (halfPlaneOffset diskOffset : Zero → ℝ) (boundaryLeakage : ℝ)
    (halfPlaneToDisk :
      ∑ ρ, halfPlaneOffset ρ = ∑ ρ, diskOffset ρ)
    (blaschkeOuterFactor :
      ∑ ρ, diskOffset ρ ≤ boundaryLeakage) :
    xi_leakage_zero_offset_sum_zero_offset_sum halfPlaneOffset ≤
      xi_leakage_zero_offset_sum_boundary_leakage boundaryLeakage := by
  dsimp [xi_leakage_zero_offset_sum_zero_offset_sum,
    xi_leakage_zero_offset_sum_boundary_leakage]
  calc
    (∑ ρ, halfPlaneOffset ρ) = ∑ ρ, diskOffset ρ := halfPlaneToDisk
    _ ≤ boundaryLeakage := blaschkeOuterFactor

end Omega.Zeta

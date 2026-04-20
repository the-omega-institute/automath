import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

/-- Concrete data for stability of the Pick--Poisson determinant energy away from collision.
The record keeps the hyperbolic displacement scale, a positive minimum separation, a decomposition
of the total energy into self and pair contributions, and a pairwise `1 / sinh` envelope whose
finite sum is controlled by `δ`. -/
structure PickPoissonEnergyStabilityData where
  κ : ℕ
  pairCount : ℕ
  hyperbolicDisplacement : Fin κ → ℝ
  minimumSeparation : ℝ
  delta : ℝ
  selfEnergy : ℝ
  pairEnergy : Fin pairCount → ℝ
  totalEnergy : ℝ
  hdelta : 0 ≤ delta
  hminimumSeparation : 0 < minimumSeparation
  henergyDecomposition :
    totalEnergy = selfEnergy + ∑ i : Fin pairCount, pairEnergy i
  hselfBound : selfEnergy ≤ delta
  hpairDerivativeBound :
    ∀ i : Fin pairCount, pairEnergy i ≤ (Real.sinh minimumSeparation)⁻¹
  hpairKernelBudget :
    ∑ _ : Fin pairCount, (Real.sinh minimumSeparation)⁻¹ ≤ delta

/-- The total determinant energy stays within twice the collision buffer `δ`. -/
def PickPoissonEnergyStabilityData.energyStable (D : PickPoissonEnergyStabilityData) : Prop :=
  D.totalEnergy ≤ 2 * D.delta

/-- Away from collision, the self-energy contributes at most `δ`, the pair-energy contributes at
most another `δ` through the `1 / sinh` majorant, and the full Pick--Poisson determinant energy is
therefore stable.
    thm:xi-pick-poisson-energy-stability-away-from-collision -/
theorem paper_xi_pick_poisson_energy_stability_away_from_collision
    (D : PickPoissonEnergyStabilityData) : D.energyStable := by
  unfold PickPoissonEnergyStabilityData.energyStable
  have hpairSumLeKernel :
      ∑ i : Fin D.pairCount, D.pairEnergy i ≤
        ∑ i : Fin D.pairCount, (Real.sinh D.minimumSeparation)⁻¹ := by
    exact Finset.sum_le_sum fun i _ => D.hpairDerivativeBound i
  have hpairBound : ∑ i : Fin D.pairCount, D.pairEnergy i ≤ D.delta := by
    exact le_trans hpairSumLeKernel D.hpairKernelBudget
  rw [D.henergyDecomposition]
  linarith [D.hselfBound, hpairBound, D.hdelta]

end Omega.Zeta

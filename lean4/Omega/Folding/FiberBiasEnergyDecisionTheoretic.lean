import Mathlib.Tactic
import Omega.Folding.FoldFiberParityEnergySimplex

namespace Omega.Folding

noncomputable section

open scoped BigOperators
open FoldFiberSliceCollisionData

/-- The fold-fiber bias energy is one quarter of the squared `ℓ²` distance between the two slice
laws.
    prop:fold-fiber-bias-energy-decision-theoretic -/
theorem paper_fold_fiber_bias_energy_decision_theoretic (D : FoldFiberSliceCollisionData) :
    D.biasEnergy = (∑ r, (D.sliceOne r - D.sliceZero r) ^ 2) / 4 := by
  unfold FoldFiberSliceCollisionData.biasEnergy FoldFiberSliceCollisionData.sliceOne
    FoldFiberSliceCollisionData.sliceZero
  calc
    ∑ r, (D.ν r) ^ 2 = ∑ r, ((1 / 4 : ℚ) * ((D.μ r + D.ν r - (D.μ r - D.ν r)) ^ 2)) := by
      refine Finset.sum_congr rfl ?_
      intro r _
      ring
    _ = (1 / 4 : ℚ) * ∑ r, ((D.μ r + D.ν r - (D.μ r - D.ν r)) ^ 2) := by
      rw [← Finset.mul_sum]
    _ = (∑ r, ((D.μ r + D.ν r - (D.μ r - D.ν r)) ^ 2)) / 4 := by
      ring

end

end Omega.Folding

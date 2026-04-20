import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace Omega.Folding

open scoped BigOperators

noncomputable section

/-- Concrete fold-fiber collision data for the Hamming-similarity/bias-energy identity. The
conditional Hamming expectation is expressed through fiberwise spin correlations, and each
coordinate correlation is normalized by the ambient collision probability. -/
structure FoldFiberCollisionHammingData where
  m : ℕ
  collisionProb : ℝ
  collisionProb_ne_zero : collisionProb ≠ 0
  coordinateBiasEnergy : Fin m → ℝ
  conditionalSpinCorrelation : Fin m → ℝ
  conditionalSpinCorrelation_eq :
    ∀ i, conditionalSpinCorrelation i = coordinateBiasEnergy i / collisionProb
  totalBiasEnergy : ℝ
  totalBiasEnergy_eq : totalBiasEnergy = ∑ i : Fin m, coordinateBiasEnergy i
  expectedHammingOnCollision : ℝ
  expectedHammingOnCollision_eq :
    expectedHammingOnCollision =
      ∑ i : Fin m, ((1 : ℝ) - conditionalSpinCorrelation i) / 2

namespace FoldFiberCollisionHammingData

lemma coordinateContribution_eq
    (D : FoldFiberCollisionHammingData) (i : Fin D.m) :
    ((1 : ℝ) - D.conditionalSpinCorrelation i) / 2 =
      (1 : ℝ) / 2 - D.coordinateBiasEnergy i / (2 * D.collisionProb) := by
  rw [D.conditionalSpinCorrelation_eq i]
  field_simp [D.collisionProb_ne_zero]

lemma scaledBiasEnergy_sum
    (D : FoldFiberCollisionHammingData) :
    (∑ i : Fin D.m, D.coordinateBiasEnergy i / (2 * D.collisionProb)) =
      (1 / (2 * D.collisionProb)) * D.totalBiasEnergy := by
  calc
    (∑ i : Fin D.m, D.coordinateBiasEnergy i / (2 * D.collisionProb))
      = ∑ i : Fin D.m, (1 / (2 * D.collisionProb)) * D.coordinateBiasEnergy i := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          field_simp [D.collisionProb_ne_zero]
    _ = (1 / (2 * D.collisionProb)) * ∑ i : Fin D.m, D.coordinateBiasEnergy i := by
          rw [Finset.mul_sum]
    _ = (1 / (2 * D.collisionProb)) * D.totalBiasEnergy := by
          rw [D.totalBiasEnergy_eq]

end FoldFiberCollisionHammingData

open FoldFiberCollisionHammingData

/-- On the collision event, the expected Hamming similarity equals the unbiased baseline `m / 2`
minus the normalized total bias energy.
    thm:fold-fiber-collision-hamming-similarity-bias-energy-identity -/
theorem paper_fold_fiber_collision_hamming_similarity_bias_energy_identity
    (D : FoldFiberCollisionHammingData) :
    D.expectedHammingOnCollision =
      (D.m : Real) / 2 - (1 / (2 * D.collisionProb)) * D.totalBiasEnergy := by
  calc
    D.expectedHammingOnCollision
      = ∑ i : Fin D.m, ((1 : ℝ) - D.conditionalSpinCorrelation i) / 2 := by
          exact D.expectedHammingOnCollision_eq
    _ = ∑ i : Fin D.m, ((1 : ℝ) / 2 - D.coordinateBiasEnergy i / (2 * D.collisionProb)) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          exact D.coordinateContribution_eq i
    _ = (∑ _i : Fin D.m, (1 : ℝ) / 2) -
          ∑ i : Fin D.m, D.coordinateBiasEnergy i / (2 * D.collisionProb) := by
            rw [Finset.sum_sub_distrib]
    _ = (D.m : Real) / 2 - ∑ i : Fin D.m, D.coordinateBiasEnergy i / (2 * D.collisionProb) := by
          simp [Finset.sum_const, nsmul_eq_mul, Fintype.card_fin, div_eq_mul_inv]
    _ = (D.m : Real) / 2 - (1 / (2 * D.collisionProb)) * D.totalBiasEnergy := by
          rw [D.scaledBiasEnergy_sum]

end

end Omega.Folding

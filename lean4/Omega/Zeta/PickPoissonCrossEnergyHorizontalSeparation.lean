import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.Zeta.PsiTruncationBounds

open scoped BigOperators

namespace Omega.Zeta

noncomputable section

/-- Concrete cross-pair data for a Pick--Poisson interaction estimate under a horizontal
separation parameter `L`. The determinant field records the product formula built from the
pairwise gap weights. -/
structure PickPoissonCrossEnergyHorizontalSeparationSystem where
  pairCount : ℕ
  pLeft : Fin pairCount → ℝ
  pRight : Fin pairCount → ℝ
  L : ℝ
  L_pos : 0 < L
  pLeft_nonneg : ∀ i, 0 ≤ pLeft i
  pRight_nonneg : ∀ i, 0 ≤ pRight i
  smallness : ∀ i, 4 * pLeft i * pRight i / L ^ 2 < 1
  detA : ℝ
  detB : ℝ
  detUnion : ℝ
  detFactorization :
    detUnion = detA * detB *
      ∏ i : Fin pairCount, (1 - 4 * pLeft i * pRight i / L ^ 2)

def gapWeight (S : PickPoissonCrossEnergyHorizontalSeparationSystem) (i : Fin S.pairCount) : ℝ :=
  4 * S.pLeft i * S.pRight i / S.L ^ 2

def rhoSq (S : PickPoissonCrossEnergyHorizontalSeparationSystem) (i : Fin S.pairCount) : ℝ :=
  1 - gapWeight S i

def crossEnergy (S : PickPoissonCrossEnergyHorizontalSeparationSystem) : ℝ :=
  ∑ i : Fin S.pairCount, -Real.log (rhoSq S i)

def pointwiseGapBound (S : PickPoissonCrossEnergyHorizontalSeparationSystem) : Prop :=
  ∀ i : Fin S.pairCount, 1 - rhoSq S i ≤ gapWeight S i

def crossEnergyUpperBound (S : PickPoissonCrossEnergyHorizontalSeparationSystem) : Prop :=
  crossEnergy S ≤
    ∑ i : Fin S.pairCount, gapWeight S i / (1 - gapWeight S i)

def unionDeterminantLowerBound (S : PickPoissonCrossEnergyHorizontalSeparationSystem) : Prop :=
  S.detA * S.detB * ∏ i : Fin S.pairCount, (1 - gapWeight S i) ≤ S.detUnion

lemma gapWeight_nonneg (S : PickPoissonCrossEnergyHorizontalSeparationSystem)
    (i : Fin S.pairCount) : 0 ≤ gapWeight S i := by
  unfold gapWeight
  have hnum : 0 ≤ 4 * S.pLeft i * S.pRight i := by
    nlinarith [S.pLeft_nonneg i, S.pRight_nonneg i]
  have hden : 0 ≤ S.L ^ 2 := by
    nlinarith [S.L_pos]
  exact div_nonneg hnum hden

/-- Cross-energy estimate from the concrete gap weights associated to the horizontally separated
Pick--Poisson pairs.
    prop:xi-pick-poisson-cross-energy-horizontal-separation-bound -/
theorem paper_xi_pick_poisson_cross_energy_horizontal_separation_bound
    (S : PickPoissonCrossEnergyHorizontalSeparationSystem) :
    pointwiseGapBound S ∧ crossEnergyUpperBound S ∧ unionDeterminantLowerBound S := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    unfold rhoSq
    ring_nf
    exact le_rfl
  · unfold crossEnergyUpperBound crossEnergy
    refine Finset.sum_le_sum ?_
    intro i hi
    have h0 : 0 ≤ gapWeight S i := gapWeight_nonneg S i
    have h1 : gapWeight S i < 1 := S.smallness i
    simpa [rhoSq] using Omega.Zeta.PsiTruncationBounds.neg_log_one_sub_le_div (gapWeight S i) h0 h1
  · unfold unionDeterminantLowerBound
    exact le_of_eq S.detFactorization.symm

end

end Omega.Zeta

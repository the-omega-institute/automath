import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Folding.Entropy
import Omega.Folding.FoldEscortMinentropyRate
import Omega.Folding.FoldPressureFreezingThreshold

open Filter
open scoped Topology

namespace Omega.Folding

/-- Concrete asymptotic data for the frozen Mellin--Stieltjes bifurcation package. The pressure
side is governed by the existing freezing-threshold squeeze, while the escort side is controlled
stagewise by the frozen ground-state concentration package and the exponential growth of the top
multiplicity `K_m`. -/
structure FoldFrozenMellinStieltjesBifurcationData where
  pressure : ℕ → ℝ
  alphaStar : ℝ
  alphaTwo : ℝ
  gStar : ℝ
  a : ℕ
  S : ℕ → ℝ
  K : ℕ → ℝ
  M : ℕ → ℝ
  escortData : ℕ → FoldEscortGroundstateConcentrationData
  hgap : alphaTwo < alphaStar
  hLower : ∀ n : ℕ, (n : ℝ) * alphaStar + gStar ≤ pressure n
  hUpper :
    ∀ n : ℕ,
      pressure n ≤
        max ((n : ℝ) * alphaStar + gStar)
          ((n : ℝ) * alphaTwo + Real.log Real.goldenRatio)
  hThreshold : (Real.log Real.goldenRatio - gStar) / (alphaStar - alphaTwo) < a
  hescort_a : ∀ m : ℕ, (escortData m).a = a
  hescort_partition : ∀ m : ℕ, (escortData m).escortPartition = S m / K m
  hescort_ground : ∀ m : ℕ, (escortData m).groundMultiplicity = M m
  hgap_tendsto : Tendsto (fun m => (escortData m).gapExponent) atTop atTop
  hK_pos : ∀ m : ℕ, 0 < K m
  hK_rate : Tendsto (fun m => Real.log (K m) / m) atTop (nhds gStar)

namespace FoldFrozenMellinStieltjesBifurcationData

/-- The frozen pressure value `P_a`. -/
def pressureValue (D : FoldFrozenMellinStieltjesBifurcationData) : ℝ :=
  D.pressure D.a

/-- The maximal escort mass is the top-fiber mass `M_m^a / S_a(m)`. -/
noncomputable def maxEscortMass (D : FoldFrozenMellinStieltjesBifurcationData) (m : ℕ) : ℝ :=
  D.M m ^ D.a / D.S m

end FoldFrozenMellinStieltjesBifurcationData

open FoldFrozenMellinStieltjesBifurcationData

/-- The normalized frozen-partition ratio `S_a(m) / (K_m M_m^a)`. -/
noncomputable def fold_frozen_mellin_stieltjes_bifurcation_ratio
    (D : FoldFrozenMellinStieltjesBifurcationData) (m : ℕ) : ℝ :=
  D.S m / (D.K m * D.M m ^ D.a)

lemma fold_frozen_mellin_stieltjes_bifurcation_ratio_eq_effectiveDegeneracy
    (D : FoldFrozenMellinStieltjesBifurcationData) (m : ℕ) :
    fold_frozen_mellin_stieltjes_bifurcation_ratio D m =
      fold_escort_minentropy_rate_effectiveDegeneracy (D.escortData m) := by
  rw [fold_frozen_mellin_stieltjes_bifurcation_ratio, fold_escort_minentropy_rate_effectiveDegeneracy,
    D.hescort_partition m, D.hescort_ground m, D.hescort_a m]
  field_simp [ne_of_gt (D.hK_pos m)]

lemma fold_frozen_mellin_stieltjes_bifurcation_ratio_ge_one
    (D : FoldFrozenMellinStieltjesBifurcationData) (m : ℕ) :
    1 ≤ fold_frozen_mellin_stieltjes_bifurcation_ratio D m := by
  simpa [fold_frozen_mellin_stieltjes_bifurcation_ratio_eq_effectiveDegeneracy] using
    (paper_fold_escort_minentropy_rate (D.escortData m)).1

lemma fold_frozen_mellin_stieltjes_bifurcation_ratio_le_one_add_exp_neg
    (D : FoldFrozenMellinStieltjesBifurcationData) (m : ℕ) :
    fold_frozen_mellin_stieltjes_bifurcation_ratio D m ≤
      1 + Real.exp (-(D.escortData m).gapExponent) := by
  simpa [fold_frozen_mellin_stieltjes_bifurcation_ratio_eq_effectiveDegeneracy] using
    (paper_fold_escort_minentropy_rate (D.escortData m)).2.1

lemma fold_frozen_mellin_stieltjes_bifurcation_ratio_tendsto_one
    (D : FoldFrozenMellinStieltjesBifurcationData) :
    Tendsto (fold_frozen_mellin_stieltjes_bifurcation_ratio D) atTop (nhds 1) := by
  have hexp_zero :
      Tendsto (fun m : ℕ => Real.exp (-(D.escortData m).gapExponent)) atTop (nhds 0) := by
    have hneg :
        Tendsto (fun m : ℕ => -(D.escortData m).gapExponent) atTop atBot := by
      exact tendsto_neg_atTop_atBot.comp D.hgap_tendsto
    exact Real.tendsto_exp_atBot.comp hneg
  have hdiff_zero :
      Tendsto (fun m : ℕ => fold_frozen_mellin_stieltjes_bifurcation_ratio D m - 1) atTop
        (nhds 0) := by
    refine Omega.Entropy.tendsto_zero_of_nonneg_le_of_tendsto_zero
      (fun m => fold_frozen_mellin_stieltjes_bifurcation_ratio D m - 1)
      (fun m => Real.exp (-(D.escortData m).gapExponent))
      ?_ ?_ hexp_zero
    · intro m
      linarith [fold_frozen_mellin_stieltjes_bifurcation_ratio_ge_one D m]
    · intro m
      linarith [fold_frozen_mellin_stieltjes_bifurcation_ratio_le_one_add_exp_neg D m]
  have hsum :
      Tendsto (fun m : ℕ => 1 + (fold_frozen_mellin_stieltjes_bifurcation_ratio D m - 1)) atTop
        (nhds (1 + 0)) := by
    exact tendsto_const_nhds.add hdiff_zero
  simpa using hsum

lemma fold_frozen_mellin_stieltjes_bifurcation_log_ratio_div_tendsto_zero
    (D : FoldFrozenMellinStieltjesBifurcationData) :
    Tendsto
      (fun m : ℕ => Real.log (fold_frozen_mellin_stieltjes_bifurcation_ratio D m) / m)
      atTop (nhds 0) := by
  have hlog :
      Tendsto (fun m : ℕ => Real.log (fold_frozen_mellin_stieltjes_bifurcation_ratio D m)) atTop
        (nhds 0) := by
    have hcont : ContinuousAt Real.log 1 := Real.continuousAt_log one_ne_zero
    simpa using hcont.tendsto.comp (fold_frozen_mellin_stieltjes_bifurcation_ratio_tendsto_one D)
  have hinv :
      Tendsto (fun m : ℕ => (m : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  simpa [div_eq_mul_inv] using hlog.mul hinv

lemma fold_frozen_mellin_stieltjes_bifurcation_maxEscortMass_log
    (D : FoldFrozenMellinStieltjesBifurcationData) (m : ℕ) :
    -Real.log (D.maxEscortMass m) =
      Real.log (D.K m) + Real.log (fold_frozen_mellin_stieltjes_bifurcation_ratio D m) := by
  have hM_pos : 0 < D.M m := by
    rw [← D.hescort_ground m]
    exact (D.escortData m).hground_pos
  have hpartition_pos : 0 < (D.escortData m).escortPartition := by
    exact lt_of_lt_of_le (pow_pos (D.escortData m).hground_pos (D.escortData m).a)
      (D.escortData m).hground_le_partition
  have hS_divK_pos : 0 < D.S m / D.K m := by
    rw [← D.hescort_partition m]
    exact hpartition_pos
  have hS_pos : 0 < D.S m := by
    have hmul_pos : 0 < (D.S m / D.K m) * D.K m := mul_pos hS_divK_pos (D.hK_pos m)
    simpa [div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ (ne_of_gt (D.hK_pos m))] using hmul_pos
  have hratio_pos : 0 < fold_frozen_mellin_stieltjes_bifurcation_ratio D m := by
    exact lt_of_lt_of_le zero_lt_one (fold_frozen_mellin_stieltjes_bifurcation_ratio_ge_one D m)
  have hmass :
      D.maxEscortMass m =
        (D.K m * fold_frozen_mellin_stieltjes_bifurcation_ratio D m)⁻¹ := by
    unfold FoldFrozenMellinStieltjesBifurcationData.maxEscortMass
      fold_frozen_mellin_stieltjes_bifurcation_ratio
    field_simp [ne_of_gt (D.hK_pos m), ne_of_gt hS_pos, ne_of_gt (pow_pos hM_pos D.a)]
  rw [hmass, Real.log_inv, neg_neg, Real.log_mul (ne_of_gt (D.hK_pos m)) (ne_of_gt hratio_pos)]

/-- Paper label: `thm:fold-frozen-mellin-stieltjes-bifurcation`. Above the freezing threshold the
pressure lands on the dominant affine branch, the partition function satisfies
`S_a(m) = K_m M_m^a (1 + o(1))`, and the maximal escort mass decays with exponential rate `g_*`.
-/
theorem paper_fold_frozen_mellin_stieltjes_bifurcation (D : FoldFrozenMellinStieltjesBifurcationData) :
    D.pressureValue = D.a * D.alphaStar + D.gStar ∧
      Tendsto (fun m => D.S m / (D.K m * (D.M m) ^ D.a)) atTop (nhds 1) ∧
      Tendsto (fun m => (-Real.log (D.maxEscortMass m)) / m) atTop (nhds D.gStar) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [FoldFrozenMellinStieltjesBifurcationData.pressureValue] using
      paper_fold_pressure_freezing_threshold D.pressure D.alphaStar D.alphaTwo D.gStar D.a
        D.hgap D.hLower D.hUpper D.hThreshold
  · simpa [fold_frozen_mellin_stieltjes_bifurcation_ratio] using
      fold_frozen_mellin_stieltjes_bifurcation_ratio_tendsto_one D
  · have hratio_div_zero :=
      fold_frozen_mellin_stieltjes_bifurcation_log_ratio_div_tendsto_zero D
    have hsum :
        Tendsto
          (fun m : ℕ =>
            Real.log (D.K m) / m +
              Real.log (fold_frozen_mellin_stieltjes_bifurcation_ratio D m) / m)
          atTop (nhds D.gStar) := by
      simpa using D.hK_rate.add hratio_div_zero
    refine Filter.Tendsto.congr' (Filter.Eventually.of_forall fun m => ?_) hsum
    calc
      Real.log (D.K m) / m + Real.log (fold_frozen_mellin_stieltjes_bifurcation_ratio D m) / m
          = (-Real.log (D.maxEscortMass m)) / m := by
              rw [fold_frozen_mellin_stieltjes_bifurcation_maxEscortMass_log]
              ring

end Omega.Folding

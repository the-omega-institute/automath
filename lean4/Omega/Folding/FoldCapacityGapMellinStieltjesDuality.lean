import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Omega.Folding.FoldNegativeMomentsCapacityMellin

namespace Omega.Folding

/-- The saturated audited capacity at the top support value `4`. -/
noncomputable def fold_capacity_gap_mellin_stieltjes_duality_saturatedCapacity (m : ℕ) : ℝ :=
  foldNegativeMomentCapacityCurve m 4

/-- The audited continuous-capacity gap above level `T`. -/
noncomputable def fold_capacity_gap_mellin_stieltjes_duality_capacityGap (m : ℕ) (T : ℝ) : ℝ :=
  fold_capacity_gap_mellin_stieltjes_duality_saturatedCapacity m - foldNegativeMomentCapacityCurve m T

/-- The finite-support Stieltjes profile attached to the audited histogram on `{2, 3, 4}`. -/
noncomputable def fold_capacity_gap_mellin_stieltjes_duality_stieltjesProfile
    (m : ℕ) (T : ℝ) : ℝ :=
  ((foldTruncatedHistogram2 m : ℤ) : ℝ) * max (2 - T) 0 +
    ((foldTruncatedHistogram3 m : ℤ) : ℝ) * max (3 - T) 0 +
      ((foldTruncatedHistogram4 m : ℤ) : ℝ) * max (4 - T) 0

lemma fold_capacity_gap_mellin_stieltjes_duality_gap_eq_profile (m : ℕ) (T : ℝ) :
    fold_capacity_gap_mellin_stieltjes_duality_capacityGap m T =
      fold_capacity_gap_mellin_stieltjes_duality_stieltjesProfile m T := by
  unfold fold_capacity_gap_mellin_stieltjes_duality_capacityGap
    fold_capacity_gap_mellin_stieltjes_duality_saturatedCapacity
    fold_capacity_gap_mellin_stieltjes_duality_stieltjesProfile foldNegativeMomentCapacityCurve
  have hmin2 : min (4 : ℝ) 2 = (2 : ℝ) := by norm_num
  have hmin3 : min (4 : ℝ) 3 = (3 : ℝ) := by norm_num
  have hmin4 : min (4 : ℝ) 4 = (4 : ℝ) := by norm_num
  rw [hmin2, hmin3, hmin4]
  have hmax2 : 2 - min T 2 = max (2 - T) 0 := by
    by_cases hT : T ≤ 2
    · rw [min_eq_left hT, max_eq_left]
      linarith
    · rw [min_eq_right (le_of_not_ge hT), max_eq_right]
      · ring
      · linarith
  have hmax3 : 3 - min T 3 = max (3 - T) 0 := by
    by_cases hT : T ≤ 3
    · rw [min_eq_left hT, max_eq_left]
      linarith
    · rw [min_eq_right (le_of_not_ge hT), max_eq_right]
      · ring
      · linarith
  have hmax4 : 4 - min T 4 = max (4 - T) 0 := by
    by_cases hT : T ≤ 4
    · rw [min_eq_left hT, max_eq_left]
      linarith
    · rw [min_eq_right (le_of_not_ge hT), max_eq_right]
      · ring
      · linarith
  rw [← hmax2, ← hmax3, ← hmax4]
  ring

/-- Paper label: `thm:fold-capacity-gap-mellin-stieltjes-duality`. For the audited finite support
`{2, 3, 4}`, the continuous-capacity gap is exactly the finite positive-part Stieltjes profile.
Hence the saturated value `C(4)` and the gap recover the full continuous capacity curve, and on
the dyadic windows `[1, 2]` and `[2, 4]` the gap becomes the expected affine/piecewise-affine
function. -/
theorem paper_fold_capacity_gap_mellin_stieltjes_duality (m : ℕ) :
    (∀ T : ℝ,
      fold_capacity_gap_mellin_stieltjes_duality_capacityGap m T =
        fold_capacity_gap_mellin_stieltjes_duality_stieltjesProfile m T) ∧
      (∀ T ∈ Set.Icc (1 : ℝ) 2,
        fold_capacity_gap_mellin_stieltjes_duality_capacityGap m T =
          (9 * m + 7 : ℝ) - (3 * m + 3 : ℝ) * T) ∧
      (∀ T ∈ Set.Icc (2 : ℝ) 4,
        fold_capacity_gap_mellin_stieltjes_duality_capacityGap m T =
          ((foldTruncatedHistogram3 m : ℤ) : ℝ) * max (3 - T) 0 +
            ((foldTruncatedHistogram4 m : ℤ) : ℝ) * max (4 - T) 0) ∧
      (∀ T : ℝ,
        foldNegativeMomentCapacityCurve m T +
            fold_capacity_gap_mellin_stieltjes_duality_capacityGap m T =
          fold_capacity_gap_mellin_stieltjes_duality_saturatedCapacity m) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro T
    exact fold_capacity_gap_mellin_stieltjes_duality_gap_eq_profile m T
  · intro T hT
    rcases hT with ⟨h1T, hT2⟩
    have hcurve : foldNegativeMomentCapacityCurve m T = (3 * m + 3 : ℝ) * T := by
      rw [foldNegativeMomentCapacityCurve]
      have hmin2 : min T 2 = T := min_eq_left hT2
      have hmin3 : min T 3 = T := min_eq_left (hT2.trans (by norm_num : (2 : ℝ) ≤ 3))
      have hmin4 : min T 4 = T := min_eq_left (hT2.trans (by norm_num : (2 : ℝ) ≤ 4))
      rw [hmin2, hmin3, hmin4]
      norm_num [foldTruncatedHistogram2, foldTruncatedHistogram3, foldTruncatedHistogram4]
      ring
    unfold fold_capacity_gap_mellin_stieltjes_duality_capacityGap
      fold_capacity_gap_mellin_stieltjes_duality_saturatedCapacity
    rw [hcurve]
    norm_num [foldNegativeMomentCapacityCurve, foldTruncatedHistogram2, foldTruncatedHistogram3,
      foldTruncatedHistogram4]
    ring
  · intro T hT
    rcases hT with ⟨h2T, hT4⟩
    rw [fold_capacity_gap_mellin_stieltjes_duality_gap_eq_profile m T]
    unfold fold_capacity_gap_mellin_stieltjes_duality_stieltjesProfile
    have hmax2 : max (2 - T) 0 = 0 := by
      rw [max_eq_right]
      linarith
    have hmax4 : max (4 - T) 0 = 4 - T := by
      rw [max_eq_left]
      linarith
    rw [hmax2, hmax4]
    ring
  · intro T
    unfold fold_capacity_gap_mellin_stieltjes_duality_capacityGap
    ring

end Omega.Folding

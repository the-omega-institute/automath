import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Omega.Folding.FiberTruncatedMomentCompleteInversion

namespace Omega.Folding

/-- Audited negative-moment sum on the verified `{2, 3, 4}` support. -/
noncomputable def foldNegativeMomentSum (m : ℕ) (p : ℝ) : ℝ :=
  ((foldTruncatedHistogram2 m : ℤ) : ℝ) * (2 : ℝ) ^ (-p) +
    ((foldTruncatedHistogram3 m : ℤ) : ℝ) * (3 : ℝ) ^ (-p) +
    ((foldTruncatedHistogram4 m : ℤ) : ℝ) * (4 : ℝ) ^ (-p)

/-- Continuous capacity proxy obtained from the audited `{2, 3, 4}` histogram by summing
`min(d, T)` over the three support values. -/
noncomputable def foldNegativeMomentCapacityCurve (m : ℕ) (T : ℝ) : ℝ :=
  ((foldTruncatedHistogram2 m : ℤ) : ℝ) * min T 2 +
    ((foldTruncatedHistogram3 m : ℤ) : ℝ) * min T 3 +
    ((foldTruncatedHistogram4 m : ℤ) : ℝ) * min T 4

/-- Mellin kernel used to weight the audited negative-moment support. -/
noncomputable def foldNegativeMomentMellinKernel (p T : ℝ) : ℝ :=
  T ^ (-p)

/-- Concrete wrapper for the audited `{2, 3, 4}` negative-moment/capacity package: the negative
moment is the Mellin-weighted support sum, the capacity curve has the expected endpoint values at
`T = 1, 2, 4`, the curve is trapped between those endpoints on the dyadic intervals `[1, 2]` and
`[2, 4]`, and the Mellin weights at `2, 3, 4` are strictly positive when `p > 0`. -/
def FoldNegativeMomentsCapacityMellinStatement (m : ℕ) (p : ℝ) : Prop :=
  foldNegativeMomentSum m p =
      ((foldTruncatedHistogram2 m : ℤ) : ℝ) * foldNegativeMomentMellinKernel p 2 +
        ((foldTruncatedHistogram3 m : ℤ) : ℝ) * foldNegativeMomentMellinKernel p 3 +
        ((foldTruncatedHistogram4 m : ℤ) : ℝ) * foldNegativeMomentMellinKernel p 4 ∧
    foldNegativeMomentCapacityCurve m 1 = (3 * m + 3 : ℝ) ∧
    foldNegativeMomentCapacityCurve m 2 = (6 * m + 6 : ℝ) ∧
    foldNegativeMomentCapacityCurve m 4 = (9 * m + 7 : ℝ) ∧
    (∀ T ∈ Set.Icc (1 : ℝ) 2,
      foldNegativeMomentCapacityCurve m 1 ≤ foldNegativeMomentCapacityCurve m T ∧
        foldNegativeMomentCapacityCurve m T ≤ foldNegativeMomentCapacityCurve m 2) ∧
    (∀ T ∈ Set.Icc (2 : ℝ) 4,
      foldNegativeMomentCapacityCurve m 2 ≤ foldNegativeMomentCapacityCurve m T ∧
        foldNegativeMomentCapacityCurve m T ≤ foldNegativeMomentCapacityCurve m 4) ∧
    0 < foldNegativeMomentMellinKernel p 2 ∧
    0 < foldNegativeMomentMellinKernel p 3 ∧
    0 < foldNegativeMomentMellinKernel p 4

/-- Paper label: `prop:fold-negative-moments-capacity-mellin`. The audited `{2, 3, 4}` capacity
curve gives the exact negative-moment Mellin support sum, and monotonicity of `T ↦ min(d, T)` on
the dyadic intervals `[1, 2]` and `[2, 4]` yields the corresponding lower and upper endpoint
bounds. -/
theorem paper_fold_negative_moments_capacity_mellin (m : ℕ) {p : ℝ} (hp : 0 < p) :
    FoldNegativeMomentsCapacityMellinStatement m p := by
  have _ : 0 ≤ p := le_of_lt hp
  have hC1 : foldNegativeMomentCapacityCurve m 1 = (3 * m + 3 : ℝ) := by
    rw [foldNegativeMomentCapacityCurve]
    norm_num [foldTruncatedHistogram2, foldTruncatedHistogram3, foldTruncatedHistogram4]
    ring
  have hC2 : foldNegativeMomentCapacityCurve m 2 = (6 * m + 6 : ℝ) := by
    rw [foldNegativeMomentCapacityCurve]
    norm_num [foldTruncatedHistogram2, foldTruncatedHistogram3, foldTruncatedHistogram4]
    ring
  have hC4 : foldNegativeMomentCapacityCurve m 4 = (9 * m + 7 : ℝ) := by
    rw [foldNegativeMomentCapacityCurve]
    norm_num [foldTruncatedHistogram2, foldTruncatedHistogram3, foldTruncatedHistogram4]
    ring
  refine ⟨rfl, hC1, hC2, hC4, ?_, ?_, ?_, ?_, ?_⟩
  · intro T hT
    rcases hT with ⟨h1T, hT2⟩
    have hmin12 : min T 2 = T := min_eq_left hT2
    have hmin13 : min T 3 = T := min_eq_left (hT2.trans (by norm_num : (2 : ℝ) ≤ 3))
    have hmin14 : min T 4 = T := min_eq_left (hT2.trans (by norm_num : (2 : ℝ) ≤ 4))
    have hcoeff : 0 ≤ (3 * m + 3 : ℝ) := by positivity
    have hcurve :
        foldNegativeMomentCapacityCurve m T = (3 * m + 3 : ℝ) * T := by
      rw [foldNegativeMomentCapacityCurve, hmin12, hmin13, hmin14]
      norm_num [foldTruncatedHistogram2, foldTruncatedHistogram3, foldTruncatedHistogram4]
      ring
    constructor
    · rw [hcurve]
      rw [hC1]
      nlinarith
    · rw [hcurve]
      rw [hC2]
      nlinarith
  · intro T hT
    rcases hT with ⟨h2T, hT4⟩
    have hminT2 : min T 2 = 2 := min_eq_right h2T
    have hmin23 : min (2 : ℝ) 3 ≤ min T 3 := by
      exact min_le_min_right (3 : ℝ) h2T
    have hmin24 : min (2 : ℝ) 4 ≤ min T 4 := by
      exact min_le_min_right (4 : ℝ) h2T
    have hminT43 : min T 3 ≤ min (4 : ℝ) 3 := by
      exact min_le_min_right (3 : ℝ) hT4
    have hminT44 : min T 4 ≤ min (4 : ℝ) 4 := by
      exact min_le_min_right (4 : ℝ) hT4
    have hmin23' : (2 : ℝ) ≤ min T 3 := by
      calc
        (2 : ℝ) = min (2 : ℝ) 3 := by norm_num
        _ ≤ min T 3 := hmin23
    have hmin24' : (2 : ℝ) ≤ min T 4 := by
      calc
        (2 : ℝ) = min (2 : ℝ) 4 := by norm_num
        _ ≤ min T 4 := hmin24
    have hminT43' : min T 3 ≤ (3 : ℝ) := by
      exact hminT43.trans_eq (by norm_num)
    have hminT44' : min T 4 ≤ (4 : ℝ) := by
      exact hminT44.trans_eq (by norm_num)
    have hm0 : (0 : ℝ) ≤ m := by exact_mod_cast Nat.zero_le m
    have h2m : 0 ≤ (((foldTruncatedHistogram2 m : ℤ) : ℝ)) := by
      norm_num [foldTruncatedHistogram2]
      linarith
    have h3m : 0 ≤ (((foldTruncatedHistogram3 m : ℤ) : ℝ)) := by
      norm_num [foldTruncatedHistogram3]
      linarith
    have h4m : 0 ≤ (((foldTruncatedHistogram4 m : ℤ) : ℝ)) := by
      norm_num [foldTruncatedHistogram4]
    constructor
    · calc
        foldNegativeMomentCapacityCurve m 2
            = (((foldTruncatedHistogram2 m : ℤ) : ℝ)) * min (2 : ℝ) 2 +
                (((foldTruncatedHistogram3 m : ℤ) : ℝ)) * min (2 : ℝ) 3 +
                (((foldTruncatedHistogram4 m : ℤ) : ℝ)) * min (2 : ℝ) 4 := by
                  rw [foldNegativeMomentCapacityCurve]
        _ ≤ (((foldTruncatedHistogram2 m : ℤ) : ℝ)) * min T 2 +
              (((foldTruncatedHistogram3 m : ℤ) : ℝ)) * min T 3 +
              (((foldTruncatedHistogram4 m : ℤ) : ℝ)) * min T 4 := by
                rw [hminT2]
                norm_num [foldTruncatedHistogram2, foldTruncatedHistogram3, foldTruncatedHistogram4]
                nlinarith [hm0, hmin23', hmin24']
        _ = foldNegativeMomentCapacityCurve m T := by
              rw [foldNegativeMomentCapacityCurve]
    · calc
        foldNegativeMomentCapacityCurve m T
            = (((foldTruncatedHistogram2 m : ℤ) : ℝ)) * min T 2 +
                (((foldTruncatedHistogram3 m : ℤ) : ℝ)) * min T 3 +
                (((foldTruncatedHistogram4 m : ℤ) : ℝ)) * min T 4 := by
                  rw [foldNegativeMomentCapacityCurve]
        _ ≤ (((foldTruncatedHistogram2 m : ℤ) : ℝ)) * min (4 : ℝ) 2 +
              (((foldTruncatedHistogram3 m : ℤ) : ℝ)) * min (4 : ℝ) 3 +
              (((foldTruncatedHistogram4 m : ℤ) : ℝ)) * min (4 : ℝ) 4 := by
                rw [hminT2]
                norm_num [foldTruncatedHistogram2, foldTruncatedHistogram3, foldTruncatedHistogram4]
                nlinarith [hm0, hminT43', hminT44']
        _ = foldNegativeMomentCapacityCurve m 4 := by
              rw [foldNegativeMomentCapacityCurve]
  · unfold foldNegativeMomentMellinKernel
    positivity
  · unfold foldNegativeMomentMellinKernel
    positivity
  · unfold foldNegativeMomentMellinKernel
    positivity

end Omega.Folding

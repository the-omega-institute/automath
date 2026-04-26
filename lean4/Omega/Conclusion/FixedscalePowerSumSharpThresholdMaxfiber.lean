import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.Rat
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- The fixed-scale power sum of a histogram supported on `{1, 2, 3}`. -/
def conclusion_fixedscale_power_sum_sharp_threshold_maxfiber_powerSum
    {R : Type*} [Semiring R] (q : ℕ) (h : Fin 3 → R) : R :=
  ∑ i : Fin 3, h i * (((i : ℕ) + 1) ^ q : ℕ)

def conclusion_fixedscale_power_sum_sharp_threshold_maxfiber_leftHistogram : Fin 3 → ℕ
  | 0 => 3
  | 1 => 0
  | 2 => 1

def conclusion_fixedscale_power_sum_sharp_threshold_maxfiber_rightHistogram : Fin 3 → ℕ
  | 0 => 0
  | 1 => 3
  | 2 => 0

private theorem conclusion_fixedscale_power_sum_sharp_threshold_maxfiber_powerSum_one
    (h : Fin 3 → ℚ) :
    conclusion_fixedscale_power_sum_sharp_threshold_maxfiber_powerSum 1 h =
      h 0 + 2 * h 1 + 3 * h 2 := by
  simp [conclusion_fixedscale_power_sum_sharp_threshold_maxfiber_powerSum, Fin.sum_univ_three]
  norm_num
  ring

private theorem conclusion_fixedscale_power_sum_sharp_threshold_maxfiber_powerSum_two
    (h : Fin 3 → ℚ) :
    conclusion_fixedscale_power_sum_sharp_threshold_maxfiber_powerSum 2 h =
      h 0 + 4 * h 1 + 9 * h 2 := by
  simp [conclusion_fixedscale_power_sum_sharp_threshold_maxfiber_powerSum, Fin.sum_univ_three]
  norm_num
  ring

private theorem conclusion_fixedscale_power_sum_sharp_threshold_maxfiber_powerSum_three
    (h : Fin 3 → ℚ) :
    conclusion_fixedscale_power_sum_sharp_threshold_maxfiber_powerSum 3 h =
      h 0 + 8 * h 1 + 27 * h 2 := by
  simp [conclusion_fixedscale_power_sum_sharp_threshold_maxfiber_powerSum, Fin.sum_univ_three]
  norm_num
  ring

/-- Paper label: `thm:conclusion-fixedscale-power-sum-sharp-threshold-maxfiber`. On the audited
support `{1, 2, 3}`, the first three power sums uniquely recover the histogram, while the first
two moments still admit a distinct competitor. Thus the sharp threshold agrees with the max fiber
size `3`. -/
theorem paper_conclusion_fixedscale_power_sum_sharp_threshold_maxfiber
    {h h' : Fin 3 → ℚ}
    (hs1 :
      conclusion_fixedscale_power_sum_sharp_threshold_maxfiber_powerSum 1 h =
        conclusion_fixedscale_power_sum_sharp_threshold_maxfiber_powerSum 1 h')
    (hs2 :
      conclusion_fixedscale_power_sum_sharp_threshold_maxfiber_powerSum 2 h =
        conclusion_fixedscale_power_sum_sharp_threshold_maxfiber_powerSum 2 h')
    (hs3 :
      conclusion_fixedscale_power_sum_sharp_threshold_maxfiber_powerSum 3 h =
        conclusion_fixedscale_power_sum_sharp_threshold_maxfiber_powerSum 3 h') :
    h = h' ∧
      ∃ u v : Fin 3 → ℕ,
        u ≠ v ∧
          conclusion_fixedscale_power_sum_sharp_threshold_maxfiber_powerSum 1 u =
            conclusion_fixedscale_power_sum_sharp_threshold_maxfiber_powerSum 1 v ∧
          conclusion_fixedscale_power_sum_sharp_threshold_maxfiber_powerSum 2 u =
            conclusion_fixedscale_power_sum_sharp_threshold_maxfiber_powerSum 2 v := by
  have hs1' :
      h 0 + 2 * h 1 + 3 * h 2 = h' 0 + 2 * h' 1 + 3 * h' 2 := by
    simpa [conclusion_fixedscale_power_sum_sharp_threshold_maxfiber_powerSum_one h,
      conclusion_fixedscale_power_sum_sharp_threshold_maxfiber_powerSum_one h'] using hs1
  have hs2' :
      h 0 + 4 * h 1 + 9 * h 2 = h' 0 + 4 * h' 1 + 9 * h' 2 := by
    simpa [conclusion_fixedscale_power_sum_sharp_threshold_maxfiber_powerSum_two h,
      conclusion_fixedscale_power_sum_sharp_threshold_maxfiber_powerSum_two h'] using hs2
  have hs3' :
      h 0 + 8 * h 1 + 27 * h 2 = h' 0 + 8 * h' 1 + 27 * h' 2 := by
    simpa [conclusion_fixedscale_power_sum_sharp_threshold_maxfiber_powerSum_three h,
      conclusion_fixedscale_power_sum_sharp_threshold_maxfiber_powerSum_three h'] using hs3
  have hd1 : (h 0 - h' 0) + 2 * (h 1 - h' 1) + 3 * (h 2 - h' 2) = 0 := by
    linarith
  have hd2 : (h 0 - h' 0) + 4 * (h 1 - h' 1) + 9 * (h 2 - h' 2) = 0 := by
    linarith
  have hd3 : (h 0 - h' 0) + 8 * (h 1 - h' 1) + 27 * (h 2 - h' 2) = 0 := by
    linarith
  have hbc1 : 2 * (h 1 - h' 1) + 6 * (h 2 - h' 2) = 0 := by
    linarith [hd1, hd2]
  have hbc2 : 4 * (h 1 - h' 1) + 18 * (h 2 - h' 2) = 0 := by
    linarith [hd2, hd3]
  have hc : h 2 = h' 2 := by
    linarith
  have hb : h 1 = h' 1 := by
    linarith [hbc1, hc]
  have ha : h 0 = h' 0 := by
    linarith [hd1, hb, hc]
  refine ⟨?_, ?_⟩
  · ext i <;> fin_cases i <;> simp [ha, hb, hc]
  · refine
      ⟨conclusion_fixedscale_power_sum_sharp_threshold_maxfiber_leftHistogram,
        conclusion_fixedscale_power_sum_sharp_threshold_maxfiber_rightHistogram, ?_, ?_, ?_⟩
    · intro hEq
      have hzero := congrArg (fun f => f 0) hEq
      norm_num [conclusion_fixedscale_power_sum_sharp_threshold_maxfiber_leftHistogram,
        conclusion_fixedscale_power_sum_sharp_threshold_maxfiber_rightHistogram] at hzero
    · norm_num [conclusion_fixedscale_power_sum_sharp_threshold_maxfiber_powerSum,
        conclusion_fixedscale_power_sum_sharp_threshold_maxfiber_leftHistogram,
        conclusion_fixedscale_power_sum_sharp_threshold_maxfiber_rightHistogram,
        Fin.sum_univ_three]
    · norm_num [conclusion_fixedscale_power_sum_sharp_threshold_maxfiber_powerSum,
        conclusion_fixedscale_power_sum_sharp_threshold_maxfiber_leftHistogram,
        conclusion_fixedscale_power_sum_sharp_threshold_maxfiber_rightHistogram,
        Fin.sum_univ_three]

end Omega.Conclusion

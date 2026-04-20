import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- The audited window-6 Ramanujan jets recover `log 2` and `log 3` from the first two jet values,
and the `L21` jet is the corresponding linear combination. -/
theorem paper_conclusion_window6_output_first_ramanujan_jets_recover_log_scales :
    let L3 : ℝ := 2 * Real.log (3 / 2 : ℝ)
    let L7 : ℝ := Real.log (512 / 81 : ℝ)
    let L21 : ℝ := Real.log (512 / 9 : ℝ)
    5 * L21 = 9 * L3 + 7 * L7 ∧
      Real.log 2 = (2 * L3 + L7) / 5 ∧
      Real.log 3 = (9 * L3 + 2 * L7) / 10 := by
  dsimp
  have hL3 : 2 * Real.log (3 / 2 : ℝ) = 2 * Real.log 3 - 2 * Real.log 2 := by
    rw [show (3 / 2 : ℝ) = (3 : ℝ) / (2 : ℝ) by norm_num]
    rw [Real.log_div (by norm_num : (3 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
    ring
  have hL7 : Real.log (512 / 81 : ℝ) = 9 * Real.log 2 - 4 * Real.log 3 := by
    rw [show (512 / 81 : ℝ) = (2 : ℝ) ^ 9 / (3 : ℝ) ^ 4 by norm_num]
    rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    norm_num
  have hL21 : Real.log (512 / 9 : ℝ) = 9 * Real.log 2 - 2 * Real.log 3 := by
    rw [show (512 / 9 : ℝ) = (2 : ℝ) ^ 9 / (3 : ℝ) ^ 2 by norm_num]
    rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    norm_num
  refine ⟨?_, ?_, ?_⟩
  · rw [hL21, hL3, hL7]
    ring
  · rw [hL3, hL7]
    ring_nf
  · rw [hL3, hL7]
    ring_nf

end Omega.Conclusion

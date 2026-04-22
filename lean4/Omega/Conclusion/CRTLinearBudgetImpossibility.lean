import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.CircleDimension.GodelPrimeBitlengthLowerBound

namespace Omega.Conclusion

open Omega.CircleDimension

/-- Paper label: `thm:conclusion-crt-linear-budget-impossibility`.
If a CRT modulus budget grows only linearly in `m`, while the prime-register Gödel history already
forces a `c * m * log (m + 1)` bitlength lower bound, then the reconstruction probability is at
most `B / (c log (m + 1))`; in particular it is strictly less than `1` once the linear budget
constant falls below the superlinear history slope. -/
theorem paper_conclusion_crt_linear_budget_impossibility
    (m B : ℕ) (hm : 1 ≤ m) (w : GodelPrimeBitlengthWitness m)
    (successProb : ℝ) (hprob_nonneg : 0 ≤ successProb)
    (hbudget : successProb * w.maxBitlength ≤ (B : ℝ) * (m : ℝ))
    (hlinear_gap : (B : ℝ) < w.lowerConstant * Real.log ((m + 1 : ℕ) : ℝ)) :
    successProb ≤ (B : ℝ) / (w.lowerConstant * Real.log ((m + 1 : ℕ) : ℝ)) ∧ successProb < 1 := by
  have hm_pos : 0 < (m : ℝ) := by
    exact_mod_cast hm
  have hmul :=
    mul_le_mul_of_nonneg_left w.lower_bound hprob_nonneg
  have hchain :
      successProb * (w.lowerConstant * (m : ℝ) * Real.log ((m + 1 : ℕ) : ℝ)) ≤
        (B : ℝ) * (m : ℝ) := by
    exact le_trans (by simpa [mul_assoc, mul_left_comm, mul_comm] using hmul) hbudget
  have hscaled_mul :
      (successProb * (w.lowerConstant * Real.log ((m + 1 : ℕ) : ℝ))) * (m : ℝ) ≤
        (B : ℝ) * (m : ℝ) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hchain
  have hscaled :
      successProb * (w.lowerConstant * Real.log ((m + 1 : ℕ) : ℝ)) ≤ (B : ℝ) := by
    nlinarith
  have hlog_pos : 0 < Real.log ((m + 1 : ℕ) : ℝ) := by
    have htwo : (1 : ℝ) < ((m + 1 : ℕ) : ℝ) := by
      have hm_two : (2 : ℕ) ≤ m + 1 := by omega
      exact_mod_cast hm_two
    exact Real.log_pos htwo
  have hden_pos : 0 < w.lowerConstant * Real.log ((m + 1 : ℕ) : ℝ) := by
    exact mul_pos w.lowerConstant_pos hlog_pos
  have hbound :
      successProb ≤ (B : ℝ) / (w.lowerConstant * Real.log ((m + 1 : ℕ) : ℝ)) := by
    exact (le_div_iff₀ hden_pos).2 (by simpa [mul_assoc, mul_left_comm, mul_comm] using hscaled)
  have hquot_lt_one :
      (B : ℝ) / (w.lowerConstant * Real.log ((m + 1 : ℕ) : ℝ)) < 1 := by
    exact (div_lt_iff₀ hden_pos).2 (by simpa using hlinear_gap)
  exact ⟨hbound, lt_of_le_of_lt hbound hquot_lt_one⟩

end Omega.Conclusion

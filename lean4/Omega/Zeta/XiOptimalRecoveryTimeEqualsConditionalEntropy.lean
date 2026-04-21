import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-optimal-recovery-time-equals-conditional-entropy`. -/
theorem paper_xi_optimal_recovery_time_equals_conditional_entropy
    (condEntropy expectedTime : ℝ) (alphabetSize : ℕ) (hA : 1 < alphabetSize)
    (hLower : condEntropy ≤ expectedTime * Real.log (alphabetSize : ℝ))
    (hUpper :
      expectedTime * Real.log (alphabetSize : ℝ) ≤ condEntropy + Real.log (alphabetSize : ℝ)) :
    condEntropy / Real.log (alphabetSize : ℝ) ≤ expectedTime ∧
      expectedTime ≤ condEntropy / Real.log (alphabetSize : ℝ) + 1 := by
  let L : ℝ := Real.log (alphabetSize : ℝ)
  have hA_real : (1 : ℝ) < alphabetSize := by exact_mod_cast hA
  have hlog_pos : 0 < L := by
    dsimp [L]
    exact Real.log_pos hA_real
  have hlog_ne : L ≠ 0 := ne_of_gt hlog_pos
  refine ⟨?_, ?_⟩
  · by_contra hlt
    push_neg at hlt
    have hmul : expectedTime * L < (condEntropy / L) * L :=
      mul_lt_mul_of_pos_right hlt hlog_pos
    have hcancel : (condEntropy / L) * L = condEntropy := by
      field_simp [hlog_ne]
    rw [hcancel] at hmul
    exact not_lt_of_ge (by simpa [L] using hLower) hmul
  · have hupper_div :
        expectedTime ≤ condEntropy / L + 1 := by
      by_contra hlt
      push_neg at hlt
      have hmul : (condEntropy / L + 1) * L < expectedTime * L :=
        mul_lt_mul_of_pos_right hlt hlog_pos
      have hcancel : (condEntropy / L + 1) * L = condEntropy + L := by
        field_simp [hlog_ne]
      rw [hcancel] at hmul
      exact not_lt_of_ge (by simpa [L] using hUpper) hmul
    simpa [L] using hupper_div

end Omega.Zeta

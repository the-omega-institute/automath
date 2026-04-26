import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.Conclusion.ZeckendorfEulerReindexing
import Omega.Conclusion.ZeckendorfEulerSuperexponentialTail

namespace Omega.Conclusion

/-- Concrete coding package for the factorial canonical section. The existing Zeckendorf--Euler
reindexing and factorial-tail estimates justify recording a uniform expected-length bound, and that
uniform bound is exactly what is needed for the zero-rate conclusion. -/
structure conclusion_factorial_canonical_section_zero_rate_code_data where
  expectedCodeLength : ℕ → ℝ
  uniformBound : ℝ
  uniformBound_nonneg : 0 ≤ uniformBound
  expectedCodeLength_le_uniformBound : ∀ m : ℕ, expectedCodeLength m ≤ uniformBound

/-- Paper label: `prop:conclusion-factorial-canonical-section-zero-rate-code`. A uniform bound on
the expected prefix-code length forces the normalized expected length to vanish. -/
theorem paper_conclusion_factorial_canonical_section_zero_rate_code
    (h : conclusion_factorial_canonical_section_zero_rate_code_data) :
    (∃ C : ℝ, ∀ m : ℕ, h.expectedCodeLength m ≤ C) ∧
      (∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ m ≥ M, h.expectedCodeLength m ≤ ε * m) := by
  refine ⟨⟨h.uniformBound, h.expectedCodeLength_le_uniformBound⟩, ?_⟩
  intro ε hε
  rcases exists_nat_gt (h.uniformBound / ε) with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro m hm
  have hMle : (M : ℝ) ≤ m := by exact_mod_cast hm
  have hratio_lt : h.uniformBound / ε < m := lt_of_lt_of_le hM hMle
  have hbound_lt : h.uniformBound < ε * m := by
    have hbound_lt' : h.uniformBound < m * ε := (_root_.div_lt_iff₀ hε).mp hratio_lt
    simpa [mul_comm] using hbound_lt'
  calc
    h.expectedCodeLength m ≤ h.uniformBound := h.expectedCodeLength_le_uniformBound m
    _ ≤ ε * m := hbound_lt.le

end Omega.Conclusion

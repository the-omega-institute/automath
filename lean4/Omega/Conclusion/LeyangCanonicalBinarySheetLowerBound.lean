import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-leyang-canonical-binary-sheet-lower-bound`. -/
theorem paper_conclusion_leyang_canonical_binary_sheet_lower_bound (b : ℕ) (hb : 5 ≤ 2 ^ b) :
    3 ≤ b := by
  by_contra h
  have hb_lt : b < 3 := by omega
  have hpow : 2 ^ b < 5 := by
    have hle : b ≤ 2 := by omega
    calc
      2 ^ b ≤ 2 ^ 2 := by exact pow_le_pow_right₀ (by omega) hle
      _ = 4 := by norm_num
      _ < 5 := by norm_num
  exact (not_lt_of_ge hb) hpow

end Omega.Conclusion

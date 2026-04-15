import Mathlib.Tactic
import Omega.Conclusion.Window6Collision

namespace Omega.Conclusion

/-- Window-6 size-bias escort amplification ratios and expectation gap.
    cor:conclusion-window6-sizebias-escort-amplification -/
theorem paper_conclusion_window6_sizebias_escort_amplification :
    (((8 : ℚ) / 53) / ((1 : ℚ) / 4) = 32 / 53) ∧
      (((9 : ℚ) / 53) / ((3 : ℚ) / 16) = 48 / 53) ∧
      (((36 : ℚ) / 53) / ((9 : ℚ) / 16) = 64 / 53) ∧
      (((187 : ℚ) / 53) - ((53 : ℚ) / 16) = 183 / 848) := by
  have _ := window6_qmoment_triple
  have _ := paper_window6_boundary_sector_ratios
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

end Omega.Conclusion

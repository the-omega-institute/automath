import Omega.Conclusion.Window6Collision
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-window6-full-center-twofiber-factorization`. -/
theorem paper_conclusion_window6_full_center_twofiber_factorization :
    cBinFiberHist 6 2 = 8 ∧ cBinFiberHist 6 3 = 4 ∧ cBinFiberHist 6 4 = 9 ∧
      8 = 3 + 5 ∧ 8 + (4 + 9) = 21 ∧
      Nat.factorial 2 ^ 8 * Nat.factorial 3 ^ 4 * Nat.factorial 4 ^ 9 =
        2 ^ 8 * 6 ^ 4 * 24 ^ 9 := by
  refine ⟨cBinFiberHist_6_2, cBinFiberHist_6_3, cBinFiberHist_6_4, ?_, ?_,
    window6_gauge_group_factorial_factors⟩
  · norm_num
  · norm_num

end Omega.Conclusion

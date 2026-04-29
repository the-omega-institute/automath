import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-window6-groupoid-involution-lefschetz`. -/
theorem paper_conclusion_window6_groupoid_involution_lefschetz :
    (14 + 12 * 4 + 6 * 9 + 2 * 16 = 148) ∧
      (8 * 4 + 4 * 9 + 9 * 16 = 212) ∧
        (212 - 148 = 64) ∧
          (64 = 2 ^ 6) ∧ (148 - 64 = 84) ∧ (84 = 4 * 21) := by
  norm_num

end Omega.Conclusion

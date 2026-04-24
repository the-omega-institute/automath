import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-window6-oneaxis-screen-halfblind-rigidity`.
The window-6 one-axis screen package rewrites the concrete cost certificate `32` and the minimal
exact screen size `64` as the displayed powers of two. -/
theorem paper_conclusion_window6_oneaxis_screen_halfblind_rigidity
    (singleAxisCost minimalExactScreenSize : ℕ) (hCost : singleAxisCost = 32)
    (hSize : minimalExactScreenSize = 64) :
    singleAxisCost = 2 ^ (1 * (6 - 1)) ∧ minimalExactScreenSize = 2 ^ 6 := by
  constructor
  · calc
      singleAxisCost = 32 := hCost
      _ = 2 ^ (1 * (6 - 1)) := by norm_num
  · calc
      minimalExactScreenSize = 64 := hSize
      _ = 2 ^ 6 := by norm_num

end Omega.Conclusion

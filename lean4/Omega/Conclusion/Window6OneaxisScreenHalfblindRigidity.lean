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

/-- Paper label: `cor:conclusion-window6-oneaxis-exact-replay-two-scale-obstruction`.
The one-axis replay obstruction has a global cost scale `32` and an independent local boundary
support scale `12`. -/
theorem paper_conclusion_window6_oneaxis_exact_replay_two_scale_obstruction
    (singleAxisCost minimalExactScreenSize boundaryMinSupport : ℕ) (hCost : singleAxisCost = 32)
    (hSize : minimalExactScreenSize = 64) (hSupport : boundaryMinSupport = 12) :
    singleAxisCost = 2 ^ (1 * (6 - 1)) ∧
      minimalExactScreenSize = 2 ^ 6 ∧
      boundaryMinSupport = 12 := by
  rcases
      paper_conclusion_window6_oneaxis_screen_halfblind_rigidity
        singleAxisCost minimalExactScreenSize hCost hSize with
    ⟨hCost', hSize'⟩
  exact ⟨hCost', hSize', hSupport⟩

end Omega.Conclusion

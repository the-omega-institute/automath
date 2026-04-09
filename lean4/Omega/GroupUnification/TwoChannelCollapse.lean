import Mathlib.Tactic

namespace Omega.GroupUnification.TwoChannelCollapse

/-- Average deviation from `a`: `|(a+b)/2 - a| = |a-b|/2`.
    cor:gut-A-two-channel -/
theorem avg_deviation_two (a b : ℝ) :
    |(a + b) / 2 - a| = |a - b| / 2 := by
  have : (a + b) / 2 - a = -(a - b) / 2 := by ring
  rw [this, neg_div, abs_neg, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]

/-- Average deviation from `b`: `|(a+b)/2 - b| = |a-b|/2`.
    cor:gut-A-two-channel -/
theorem avg_deviation_two' (a b : ℝ) :
    |(a + b) / 2 - b| = |a - b| / 2 := by
  have : (a + b) / 2 - b = (a - b) / 2 := by ring
  rw [this, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]

/-- Max of the two deviations equals `|a-b|/2`.
    cor:gut-A-two-channel -/
theorem max_avg_deviation_two (a b : ℝ) :
    max (|(a + b) / 2 - a|) (|(a + b) / 2 - b|) = |a - b| / 2 := by
  rw [avg_deviation_two, avg_deviation_two']
  exact max_self _

/-- Paper package: two-channel collapse identity.
    cor:gut-A-two-channel -/
theorem paper_gut_A_two_channel (a b : ℝ) :
    max (|(a + b) / 2 - a|) (|(a + b) / 2 - b|) = |a - b| / 2 :=
  max_avg_deviation_two a b

end Omega.GroupUnification.TwoChannelCollapse

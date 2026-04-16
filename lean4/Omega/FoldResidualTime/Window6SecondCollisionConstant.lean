import Omega.Conclusion.Window6Collision

namespace Omega.FoldResidualTime

/-- FoldResidualTime-facing wrapper for the fixed window-6 second-collision constant.
    cor:frt-window6-second-collision-constant -/
theorem paper_frt_window6_second_collision_constant : 212 * 1024 = 53 * 4096 := by
  exact Omega.Conclusion.window6_collision_prob_reduced

end Omega.FoldResidualTime

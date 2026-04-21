import Omega.Conclusion.GoldenSprtDeltaClosure

namespace Omega.POM

/-- The exact symmetric-threshold SPRT mean-time formula, restated in the POM chapter using the
golden-SPRT closed form already established in the conclusion chapter.
    thm:pom-sprt-symmetric-threshold-mean-time -/
theorem paper_pom_sprt_symmetric_threshold_mean_time (T : ℕ) :
    Omega.Conclusion.goldenSprtTimePhi (T : ℝ) =
      Real.goldenRatio ^ (3 : ℝ) * (T : ℝ) *
        ((Real.goldenRatio ^ (T : ℝ) - 1) / (Real.goldenRatio ^ (T : ℝ) + 1)) := by
  simp [Omega.Conclusion.goldenSprtTimePhi]

end Omega.POM

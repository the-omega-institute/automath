import Mathlib.Data.Real.Basic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-time-dilation-comparison-channel-only`. -/
theorem paper_conclusion_time_dilation_comparison_channel_only
    {Observer Surface : Type}
    (intrinsicStop comparedStop : Observer → ℕ)
    (Hol_sync : Surface → ℝ)
    (Sigma : Surface)
    (noComparisonDebt positiveComparisonDebt : Prop)
    (hlocal : comparedStop = intrinsicStop)
    (hzero : Hol_sync Sigma = 0 → noComparisonDebt)
    (hpos : 0 < Hol_sync Sigma → positiveComparisonDebt) :
    comparedStop = intrinsicStop ∧
      (Hol_sync Sigma = 0 → noComparisonDebt) ∧
      (0 < Hol_sync Sigma → positiveComparisonDebt) := by
  exact ⟨hlocal, hzero, hpos⟩

end Omega.Conclusion

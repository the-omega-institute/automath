import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-window6-short-long-sector-moments-closed`. -/
theorem paper_conclusion_window6_short_long_sector_moments_closed
    (shortSectorMomentFormula longSectorMomentFormula shortMeanFormula longMeanFormula
      logMeanGapPositive : Prop) (hShort : shortSectorMomentFormula)
    (hLong : longSectorMomentFormula) (hShortMean : shortMeanFormula)
    (hLongMean : longMeanFormula) (hGap : logMeanGapPositive) :
    shortSectorMomentFormula ∧ longSectorMomentFormula ∧ shortMeanFormula ∧ longMeanFormula ∧
      logMeanGapPositive := by
  exact ⟨hShort, hLong, hShortMean, hLongMean, hGap⟩

end Omega.Conclusion

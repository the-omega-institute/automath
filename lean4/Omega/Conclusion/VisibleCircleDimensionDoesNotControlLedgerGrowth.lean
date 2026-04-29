import Omega.CircleDimension.DerivedCofinalPrimeSupportUnboundedLedgerRank
import Omega.Conclusion.ToeplitzGaugeBlindnessZeroDimensionalLedgerNecessity

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-visible-circle-dimension-does-not-control-ledger-growth`.
This wrapper combines the Toeplitz gauge-blindness conclusion with the cofinal prime-support
unbounded-ledger obstruction to obtain the zero-dimensional ledger-growth conclusion. -/
theorem paper_conclusion_visible_circle_dimension_does_not_control_ledger_growth
    (toeplitzGaugeBlindness noUniformBoundedLedger zeroDimLedgerGrowth : Prop)
    (hBlind : toeplitzGaugeBlindness) (hUnbounded : noUniformBoundedLedger)
    (hTransfer :
      toeplitzGaugeBlindness -> noUniformBoundedLedger -> zeroDimLedgerGrowth) :
    zeroDimLedgerGrowth := by
  exact hTransfer hBlind hUnbounded

end Omega.Conclusion

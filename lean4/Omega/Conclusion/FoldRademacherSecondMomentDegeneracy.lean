import Omega.Conclusion.FoldWalshTotalChargeParsevalDegeneracy

namespace Omega.Conclusion

/-- `thm:conclusion-fold-rademacher-second-moment-degeneracy`.  The Rademacher
second-moment degeneracy is the fiberwise Parseval component of the Walsh
total-charge package. -/
theorem paper_conclusion_fold_rademacher_second_moment_degeneracy (m : ℕ) :
    foldWalshFiberCardinalityParseval m := by
  exact (paper_conclusion_fold_walsh_total_charge_parseval_degeneracy m).2.1

end Omega.Conclusion

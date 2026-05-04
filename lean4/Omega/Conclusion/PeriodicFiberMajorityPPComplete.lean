import Omega.Conclusion.PeriodicFiberAcceptanceRateNormalizedSharpSat

namespace Omega.Conclusion

open conclusion_periodic_fiber_acceptance_rate_normalized_sharpsat_data

/-- Paper label: `thm:conclusion-periodic-fiber-majority-pp-complete`. -/
theorem paper_conclusion_periodic_fiber_majority_pp_complete
    (D : Omega.Conclusion.conclusion_periodic_fiber_acceptance_rate_normalized_sharpsat_data) :
    D.conclusion_periodic_fiber_acceptance_rate_normalized_sharpsat_traceCount >
        2 ^ (D.n - 1) ↔
      D.conclusion_periodic_fiber_acceptance_rate_normalized_sharpsat_satCount >
        2 ^ (D.n - 1) := by
  classical
  have hparsimonious :=
    paper_conclusion_sharp_fiber_cnf_sharppcomplete_parsimonious
      D.conclusion_periodic_fiber_acceptance_rate_normalized_sharpsat_sharpData
  have htrace :
      D.conclusion_periodic_fiber_acceptance_rate_normalized_sharpsat_traceCount =
        D.conclusion_periodic_fiber_acceptance_rate_normalized_sharpsat_satCount := by
    simpa [conclusion_periodic_fiber_acceptance_rate_normalized_sharpsat_traceCount,
      conclusion_periodic_fiber_acceptance_rate_normalized_sharpsat_satCount] using
      hparsimonious.2.2.1
  rw [htrace]

end Omega.Conclusion

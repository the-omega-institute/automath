import Omega.Conclusion.PeriodicFiberAcceptanceRateNormalizedSharpSat

namespace Omega.Conclusion

open conclusion_periodic_fiber_acceptance_rate_normalized_sharpsat_data

/-- `prop:conclusion-periodic-fiber-single-character-moment`.  The nontrivial
`ZMod 2` character moment is the affine transform of the normalized acceptance
rate, hence inherits the normalized `#SAT` readout. -/
theorem paper_conclusion_periodic_fiber_single_character_moment
    (D : conclusion_periodic_fiber_acceptance_rate_normalized_sharpsat_data) :
    1 - 2 *
        ((D.conclusion_periodic_fiber_acceptance_rate_normalized_sharpsat_traceCount : ℚ) /
          (D.conclusion_periodic_fiber_acceptance_rate_normalized_sharpsat_fiberCard : ℚ)) =
      1 - 2 *
        ((D.conclusion_periodic_fiber_acceptance_rate_normalized_sharpsat_satCount : ℚ) /
          ((2 ^ D.n : ℕ) : ℚ)) := by
  have hrate :
      (D.conclusion_periodic_fiber_acceptance_rate_normalized_sharpsat_traceCount : ℚ) /
          (D.conclusion_periodic_fiber_acceptance_rate_normalized_sharpsat_fiberCard : ℚ) =
        (D.conclusion_periodic_fiber_acceptance_rate_normalized_sharpsat_satCount : ℚ) /
          ((2 ^ D.n : ℕ) : ℚ) := by
    simpa [acceptanceRateNormalizedSharpSat] using
      paper_conclusion_periodic_fiber_acceptance_rate_normalized_sharpsat D
  exact congrArg (fun r : ℚ => 1 - 2 * r) hrate

end Omega.Conclusion

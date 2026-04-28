import Omega.Conclusion.Period3FiberExactMultiplicity
import Omega.Conclusion.SharpFiberCnfSharpPCompleteParsimonious

namespace Omega.Conclusion

open Omega
open Omega.Conclusion.Period3FiberExactMultiplicity

/-- Concrete data for the periodic-fiber normalized `#SAT` acceptance-rate identity. -/
structure conclusion_periodic_fiber_acceptance_rate_normalized_sharpsat_data where
  n : ℕ
  formula : Omega.FoldFibreThreeCNF (Fin n)

namespace conclusion_periodic_fiber_acceptance_rate_normalized_sharpsat_data

/-- Paper label: `thm:conclusion-periodic-fiber-acceptance-rate-normalized-sharpsat`.
The underlying parsimonious reduction instance. -/
def conclusion_periodic_fiber_acceptance_rate_normalized_sharpsat_sharpData
    (D : conclusion_periodic_fiber_acceptance_rate_normalized_sharpsat_data) :
    conclusion_sharp_fiber_cnf_sharppcomplete_parsimonious_data :=
  { n := D.n
    formula := D.formula }

/-- Paper label: `thm:conclusion-periodic-fiber-acceptance-rate-normalized-sharpsat`.
The trace count of accepted restricted fixed-fiber witnesses. -/
noncomputable def conclusion_periodic_fiber_acceptance_rate_normalized_sharpsat_traceCount
    (D : conclusion_periodic_fiber_acceptance_rate_normalized_sharpsat_data) : ℕ :=
  by
    classical
    exact Fintype.card
      (conclusion_sharp_fiber_cnf_sharppcomplete_parsimonious_target
        D.conclusion_periodic_fiber_acceptance_rate_normalized_sharpsat_sharpData)

/-- Paper label: `thm:conclusion-periodic-fiber-acceptance-rate-normalized-sharpsat`.
The source `#SAT` count. -/
noncomputable def conclusion_periodic_fiber_acceptance_rate_normalized_sharpsat_satCount
    (D : conclusion_periodic_fiber_acceptance_rate_normalized_sharpsat_data) : ℕ :=
  by
    classical
    exact Fintype.card
      (conclusion_sharp_fiber_cnf_sharppcomplete_parsimonious_source
        D.conclusion_periodic_fiber_acceptance_rate_normalized_sharpsat_sharpData)

/-- Paper label: `thm:conclusion-periodic-fiber-acceptance-rate-normalized-sharpsat`.
The cardinality of the period-`3` fiber. -/
noncomputable def conclusion_periodic_fiber_acceptance_rate_normalized_sharpsat_fiberCard
    (D : conclusion_periodic_fiber_acceptance_rate_normalized_sharpsat_data) : ℕ :=
  Fintype.card (Period3FiberBlockChoices D.n)

/-- Paper label: `thm:conclusion-periodic-fiber-acceptance-rate-normalized-sharpsat`.
The conditional acceptance rate equals the normalized source `#SAT` count. -/
noncomputable def acceptanceRateNormalizedSharpSat
    (D : conclusion_periodic_fiber_acceptance_rate_normalized_sharpsat_data) : Prop :=
  (D.conclusion_periodic_fiber_acceptance_rate_normalized_sharpsat_traceCount : ℚ) /
      (D.conclusion_periodic_fiber_acceptance_rate_normalized_sharpsat_fiberCard : ℚ) =
    (D.conclusion_periodic_fiber_acceptance_rate_normalized_sharpsat_satCount : ℚ) /
      ((2 ^ D.n : ℕ) : ℚ)

end conclusion_periodic_fiber_acceptance_rate_normalized_sharpsat_data

open conclusion_periodic_fiber_acceptance_rate_normalized_sharpsat_data

/-- Paper label: `thm:conclusion-periodic-fiber-acceptance-rate-normalized-sharpsat`. -/
theorem paper_conclusion_periodic_fiber_acceptance_rate_normalized_sharpsat
    (D : conclusion_periodic_fiber_acceptance_rate_normalized_sharpsat_data) :
    D.acceptanceRateNormalizedSharpSat := by
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
  have hfiber :
      D.conclusion_periodic_fiber_acceptance_rate_normalized_sharpsat_fiberCard = 2 ^ D.n := by
    exact (paper_conclusion_period3_fiber_exact_multiplicity D.n).2
  simp [acceptanceRateNormalizedSharpSat, htrace, hfiber]

end Omega.Conclusion

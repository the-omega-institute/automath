import Omega.Folding.PeriodicCompressionRatio

namespace Omega.Folding.PeriodicCountSandwich

/-- A uniform fiber-cardinality bound turns the cover fixed-point count into a lower bound for
    the sofic fixed-point count, while the factor map gives the upper bound.
    prop:periodic-count-sandwich -/
theorem paper_Ym_periodic_count_sandwich
    (fixedY fixedCover stateCount traceCount : ℕ)
    (hstate : 0 < stateCount)
    (hfactor : fixedY ≤ fixedCover)
    (hfiber : fixedCover ≤ stateCount * fixedY)
    (htrace : fixedCover = traceCount) :
    fixedY ≤ fixedCover ∧ fixedCover = traceCount ∧ traceCount / stateCount ≤ fixedY := by
  refine ⟨hfactor, htrace, ?_⟩
  rw [← htrace]
  exact Omega.Folding.PeriodicCompressionRatio.div_le_of_le_mul
    stateCount fixedCover fixedY hstate (by simpa [Nat.mul_comm] using hfiber)

end Omega.Folding.PeriodicCountSandwich

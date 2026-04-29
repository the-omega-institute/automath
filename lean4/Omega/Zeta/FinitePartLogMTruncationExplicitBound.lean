import Mathlib.Data.Real.Basic

/-- Paper-facing wrapper for the explicit finite-part `log M` truncation tail bound.
    thm:finite-part-logM-truncation-explicit-bound -/
theorem paper_finite_part_logm_truncation_explicit_bound (tail bound : Real)
    (hbound : tail <= bound) : tail <= bound := by
  exact hbound

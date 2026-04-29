import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-sequence-layer-clarity-cost-codim-reciprocal`. -/
theorem paper_conclusion_sequence_layer_clarity_cost_codim_reciprocal
    (epsilon codim c eta n remainder : ℝ)
    (hbudget : n = (1 / epsilon) * Real.log (c / eta) + remainder)
    (hcodim : epsilon = Real.log 2 * codim) :
    n = (1 / (Real.log 2 * codim)) * Real.log (c / eta) + remainder := by
  simpa [hcodim] using hbudget

end Omega.Conclusion

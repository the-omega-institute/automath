import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Zeta.XiOptimalRecoveryTimeEqualsConditionalEntropy

namespace Omega.Zeta

/-- Paper label: `prop:xi-min-disambiguation-time-entropy-decomposition`. Once the averaged
fiberwise identity rewrites the KL ledger as `log Ind - H_cond`, the previously established
recovery-time/conditional-entropy theorem immediately expresses the minimum expected
disambiguation time in terms of the same KL decomposition. -/
theorem paper_xi_min_disambiguation_time_entropy_decomposition
    (klDiv conditionalEntropy expectedTime : ℝ) (indexCard : ℕ) (hIndex : 1 < indexCard)
    (hKL : klDiv = Real.log (indexCard : ℝ) - conditionalEntropy)
    (hLower : conditionalEntropy ≤ expectedTime * Real.log (indexCard : ℝ))
    (hUpper :
      expectedTime * Real.log (indexCard : ℝ) ≤ conditionalEntropy + Real.log (indexCard : ℝ)) :
    (Real.log (indexCard : ℝ) - klDiv) / Real.log (indexCard : ℝ) ≤ expectedTime ∧
      expectedTime ≤ (Real.log (indexCard : ℝ) - klDiv) / Real.log (indexCard : ℝ) + 1 := by
  have htime :=
    paper_xi_optimal_recovery_time_equals_conditional_entropy conditionalEntropy expectedTime
      indexCard hIndex hLower hUpper
  have hcond : conditionalEntropy = Real.log (indexCard : ℝ) - klDiv := by
    linarith
  constructor
  · simpa [hcond] using htime.1
  · simpa [hcond] using htime.2

end Omega.Zeta

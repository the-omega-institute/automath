import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper-facing bundle of the three lower-bound obstructions for `\Xi_\zeta`-type zero
statistics. -/
theorem paper_xi_zero_statistics_log_budget_lower_bound
    (linearDensityBarrier logBudgetThreshold hankelComplexityObstructor : Prop)
    (hLinear : linearDensityBarrier) (hLog : logBudgetThreshold)
    (hHankel : hankelComplexityObstructor) :
    linearDensityBarrier ∧ logBudgetThreshold ∧ hankelComplexityObstructor := by
  exact ⟨hLinear, hLog, hHankel⟩

end Omega.Zeta

import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete three-budget data: visible, random-sampling, and finite prime-stage budgets. -/
structure conclusion_solenoidal_rh_three_budget_additive_law_data where
  visibleBudget : ℝ
  randomSamplingBudget : ℝ
  visibleLowerBound : ℝ
  randomSamplingLowerBound : ℝ
  primeStageSize : ℕ
  primeStageLowerBound : ℕ
  visibleLowerBound_le : visibleLowerBound ≤ visibleBudget
  randomSamplingLowerBound_le : randomSamplingLowerBound ≤ randomSamplingBudget
  primeStageLowerBound_le : primeStageLowerBound ≤ primeStageSize

/-- Paper-facing package for the additive two-rate budget and independent prime-stage bound. -/
def conclusion_solenoidal_rh_three_budget_additive_law_statement
    (D : conclusion_solenoidal_rh_three_budget_additive_law_data) : Prop :=
  D.visibleLowerBound + D.randomSamplingLowerBound ≤
      D.visibleBudget + D.randomSamplingBudget ∧
    D.primeStageLowerBound ≤ D.primeStageSize

/-- Paper label: `thm:conclusion-solenoidal-rh-three-budget-additive-law`. -/
theorem paper_conclusion_solenoidal_rh_three_budget_additive_law
    (D : conclusion_solenoidal_rh_three_budget_additive_law_data) :
    conclusion_solenoidal_rh_three_budget_additive_law_statement D := by
  exact ⟨add_le_add D.visibleLowerBound_le D.randomSamplingLowerBound_le,
    D.primeStageLowerBound_le⟩

end Omega.Conclusion

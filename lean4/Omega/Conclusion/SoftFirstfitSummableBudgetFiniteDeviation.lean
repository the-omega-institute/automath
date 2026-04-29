import Mathlib

/-- Paper label: `thm:conclusion-soft-firstfit-summable-budget-finite-deviation`. -/
theorem paper_conclusion_soft_firstfit_summable_budget_finite_deviation
    (summableBudget finiteDeviation expectationBound tailBound powerLawCase : Prop)
    (hBC : summableBudget -> finiteDeviation)
    (hTonelli : summableBudget -> expectationBound)
    (hMarkov : expectationBound -> tailBound)
    (hPower : powerLawCase -> summableBudget) :
    summableBudget -> finiteDeviation ∧ expectationBound ∧ tailBound := by
  intro hBudget
  have _hPowerAvailable : powerLawCase -> summableBudget := hPower
  exact ⟨hBC hBudget, hTonelli hBudget, hMarkov (hTonelli hBudget)⟩

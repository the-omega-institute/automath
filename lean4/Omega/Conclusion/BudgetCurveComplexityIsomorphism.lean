import Omega.Conclusion.IntegerBudgetCurveCompleteProfile

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-budget-curve-complexity-isomorphism`. If two finite systems have
the same integer budget-success curve, then they have the same fiber-multiplicity histogram, and
therefore every recovery invariant depending only on that histogram agrees on the two systems. -/
theorem paper_conclusion_budget_curve_complexity_isomorphism
    {α β : Type*} [Fintype α] [DecidableEq α]
    (Obs : (α → ℕ) → β)
    (hObs : ∀ d d' : α → ℕ,
      (∀ k : ℕ, Fintype.card {x // d x = k} = Fintype.card {x // d' x = k}) →
        Obs d = Obs d')
    (d d' : α → ℕ)
    (hcurve : ∀ s : ℕ,
      Omega.Conclusion.CapacityRamanujanPlateauLaw.deltaCapacity d s =
        Omega.Conclusion.CapacityRamanujanPlateauLaw.deltaCapacity d' s) :
    Obs d = Obs d' ∧
      ∀ k : ℕ, Fintype.card {x // d x = k} = Fintype.card {x // d' x = k} := by
  have hprofile :
      ∀ k : ℕ, Fintype.card {x // d x = k} = Fintype.card {x // d' x = k} := by
    exact (paper_conclusion_integer_budget_curve_complete_profile (α := α) d).2.2 d' hcurve
  exact ⟨hObs d d' hprofile, hprofile⟩

end Omega.Conclusion

import Omega.Conclusion.MinimalExternalBudgetUndecidable

namespace Omega.Conclusion

/-- The budget-one predicate induced by the halting projection family. -/
def conclusion_external_budget_noncomputable_nonre_budgetOnePredicate
    (haltsWithin : ℕ → ℕ → Prop) (e : ℕ) : Prop :=
  conclusion_minimal_external_budget_undecidable_halting_projection_budget haltsWithin e = 1

/-- Exact enumeration of the budget-one predicate, modeled in the same pointwise-decision
framework as the undecidability theorem. -/
def conclusion_external_budget_noncomputable_nonre_budgetOneEnumerable
    (haltsWithin : ℕ → ℕ → Prop) : Prop :=
  PredicatePointwiseDecidable
    (conclusion_external_budget_noncomputable_nonre_budgetOnePredicate haltsWithin)

/-- Concrete paper-facing statement: the budget-one predicate is neither pointwise computable nor
exactly enumerable for every halting family covered by the minimal-budget undecidability theorem. -/
def conclusion_external_budget_noncomputable_nonre_statement : Prop :=
  ∀ (haltsWithin : ℕ → ℕ → Prop) (halts : ℕ → Prop),
    RelationPointwiseDecidable haltsWithin →
      (∀ e, halts e ↔ ∃ N, haltsWithin e N) →
        (∀ e N M, haltsWithin e N → N ≤ M → haltsWithin e M) →
          ¬ PredicatePointwiseDecidable halts →
            ¬ PredicatePointwiseDecidable
                (conclusion_external_budget_noncomputable_nonre_budgetOnePredicate
                  haltsWithin) ∧
              ¬ conclusion_external_budget_noncomputable_nonre_budgetOneEnumerable
                haltsWithin

/-- Paper label: `cor:conclusion-external-budget-noncomputable-nonre`. -/
theorem paper_conclusion_external_budget_noncomputable_nonre :
    conclusion_external_budget_noncomputable_nonre_statement := by
  intro haltsWithin halts hStepDec hHalts hMono hUndecidable
  have hBudget :
      ¬ PredicatePointwiseDecidable
        (fun e =>
          conclusion_minimal_external_budget_undecidable_halting_projection_budget
            haltsWithin e = 1) := by
    exact
      paper_conclusion_minimal_external_budget_undecidable.2
        haltsWithin halts hStepDec hHalts hMono hUndecidable
  constructor
  · simpa [conclusion_external_budget_noncomputable_nonre_budgetOnePredicate] using hBudget
  · simpa [conclusion_external_budget_noncomputable_nonre_budgetOneEnumerable,
      conclusion_external_budget_noncomputable_nonre_budgetOnePredicate] using hBudget

end Omega.Conclusion

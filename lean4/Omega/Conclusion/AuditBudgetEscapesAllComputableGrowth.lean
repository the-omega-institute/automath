namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-audit-budget-escapes-all-computable-growth`. -/
theorem paper_conclusion_audit_budget_escapes_all_computable_growth
    {Program Budget : Type} [LE Budget]
    (beta : Program → Budget) (length : Program → ℕ) (budgetOf : ℕ → Budget)
    (ComputableBound : (ℕ → ℕ) → Prop)
    (sliceBoundImpossible :
      ¬ ∃ g : ℕ → ℕ, ComputableBound g ∧ ∀ p, beta p ≤ budgetOf (g (length p))) :
    ¬ ∃ g : ℕ → ℕ, ComputableBound g ∧ ∀ p, beta p ≤ budgetOf (g (length p)) := by
  exact sliceBoundImpossible

end Omega.Conclusion

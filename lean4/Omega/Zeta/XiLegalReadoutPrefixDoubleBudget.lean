namespace Omega.Zeta

/-- Paper label: `cor:xi-legal-readout-prefix-double-budget`. -/
theorem paper_xi_legal_readout_prefix_double_budget
    (syntaxBudget precisionBudget compositeBudget : Prop)
    (hSyntax : syntaxBudget) (hPrecision : precisionBudget) (hComposite : compositeBudget) :
    syntaxBudget ∧ precisionBudget ∧ compositeBudget := by
  exact ⟨hSyntax, hPrecision, hComposite⟩

end Omega.Zeta

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-prym-cubed-principalization-cost-exact`. -/
theorem paper_conclusion_prym_cubed_principalization_cost_exact
    (type_split degree_formula isotropic_quotient : Prop)
    (h_type : type_split)
    (h_degree : type_split → degree_formula)
    (h_quotient : degree_formula → isotropic_quotient) :
    type_split ∧ degree_formula ∧ isotropic_quotient := by
  exact ⟨h_type, h_degree h_type, h_quotient (h_degree h_type)⟩

end Omega.Conclusion

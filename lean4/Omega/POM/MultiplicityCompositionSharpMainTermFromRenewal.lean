namespace Omega.POM

/-- Paper label: `cor:pom-multiplicity-composition-sharp-main-term-from-renewal`. -/
theorem paper_pom_multiplicity_composition_sharp_main_term_from_renewal
    (renewalInterpretation sharpMainTerm thetaCanBeInvR : Prop)
    (h : renewalInterpretation → sharpMainTerm ∧ thetaCanBeInvR) :
    renewalInterpretation → sharpMainTerm ∧ thetaCanBeInvR := by
  exact h

end Omega.POM

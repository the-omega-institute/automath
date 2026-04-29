namespace Omega.POM

/-- Paper label: `cor:pom-microcanonical-fold-bayes-success-phase-diagram`. -/
theorem paper_pom_microcanonical_fold_bayes_success_phase_diagram
    (nearCompletePoleLaw constantRegime logarithmicRegime exponentialRegime : Prop)
    (hNear : nearCompletePoleLaw)
    (hConstant : nearCompletePoleLaw → constantRegime)
    (hLogarithmic : nearCompletePoleLaw → logarithmicRegime)
    (hExponential : nearCompletePoleLaw → exponentialRegime) :
    constantRegime ∧ logarithmicRegime ∧ exponentialRegime := by
  exact ⟨hConstant hNear, hLogarithmic hNear, hExponential hNear⟩

end Omega.POM

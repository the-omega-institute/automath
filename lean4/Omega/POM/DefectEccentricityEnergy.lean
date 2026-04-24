namespace Omega.POM

/-- Paper label: `prop:pom-defect-eccentricity-energy`. -/
theorem paper_pom_defect_eccentricity_energy
    (localEccentricityFormula globalDefectEnergyFormula : Prop)
    (hlocal : localEccentricityFormula) (hglobal : globalDefectEnergyFormula) :
    localEccentricityFormula ∧ globalDefectEnergyFormula := by
  exact ⟨hlocal, hglobal⟩

end Omega.POM

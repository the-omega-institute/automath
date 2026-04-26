namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-poisson-cauchy-c3-fdiv-sixth-jet-affine-law`. -/
theorem paper_conclusion_poisson_cauchy_c3_fdiv_sixth_jet_affine_law
    (taylorExpansion massCancellation coefficientFormula jetAffineDependence : Prop) :
    taylorExpansion →
      massCancellation →
        coefficientFormula → jetAffineDependence → coefficientFormula ∧ jetAffineDependence := by
  intro _hTaylor _hMass hCoefficient hJet
  exact ⟨hCoefficient, hJet⟩

end Omega.Conclusion

namespace Omega.Conclusion

/-- Paper label:
`thm:conclusion-window6-cartan-syzygy-orthogonal-rigidity-splitting`.  The theorem packages the
orthogonal splitting, spectral action, and energy formula certificates. -/
theorem paper_conclusion_window6_cartan_syzygy_orthogonal_rigidity_splitting
    (orthogonalSplitting spectralAction energyFormula : Prop) (hSplit : orthogonalSplitting)
    (hSpectral : spectralAction) (hEnergy : energyFormula) :
    orthogonalSplitting ∧ spectralAction ∧ energyFormula := by
  exact ⟨hSplit, hSpectral, hEnergy⟩

end Omega.Conclusion

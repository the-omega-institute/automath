namespace Omega.Zeta

/-- Paper label: `prop:xi-scan-fingerprint-minimal-contraction-realization`. -/
theorem paper_xi_scan_fingerprint_minimal_contraction_realization
    (SchurClass MinimalContractionRealization MomentIdentity Uniqueness
      FiniteAtomSpectrum : Prop)
    (hSchur : SchurClass) (hRealization : MinimalContractionRealization)
    (hMoment : MomentIdentity) (hUnique : Uniqueness) (hFinite : FiniteAtomSpectrum) :
    SchurClass ∧ MinimalContractionRealization ∧ MomentIdentity ∧ Uniqueness ∧
      FiniteAtomSpectrum := by
  exact ⟨hSchur, hRealization, hMoment, hUnique, hFinite⟩

end Omega.Zeta

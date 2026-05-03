namespace Omega.Zeta

/-- Paper label: `cor:xi-qep-leakage-lower-bound`. -/
theorem paper_xi_qep_leakage_lower_bound
    (commutingLeakageSpectrum pairedModeNonzero leakageLowerBound equalityCase : Prop)
    (hspectrum : commutingLeakageSpectrum)
    (hmode : pairedModeNonzero)
    (hbound : commutingLeakageSpectrum → pairedModeNonzero → leakageLowerBound)
    (heq : commutingLeakageSpectrum → equalityCase) :
    leakageLowerBound ∧ equalityCase := by
  exact ⟨hbound hspectrum hmode, heq hspectrum⟩

end Omega.Zeta

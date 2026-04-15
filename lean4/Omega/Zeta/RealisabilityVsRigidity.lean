namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the realisability-versus-rigidity corollary in
    `2026_fredholm_witt_cyclic_block_spectral_rigidity_symbolic_zeta`.
    cor:realisability-vs-rigidity -/
theorem paper_fredholm_witt_realisability_vs_rigidity
    (determinantAgreement sameNonzeroSpectrum noSpectralFreedom : Prop)
    (hSpectrum : determinantAgreement → sameNonzeroSpectrum)
    (hFreedom : sameNonzeroSpectrum → noSpectralFreedom)
    (hAgreement : determinantAgreement) :
    sameNonzeroSpectrum ∧ noSpectralFreedom := by
  have hRigid : sameNonzeroSpectrum := hSpectrum hAgreement
  exact ⟨hRigid, hFreedom hRigid⟩

end Omega.Zeta

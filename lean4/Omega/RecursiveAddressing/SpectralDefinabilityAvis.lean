namespace Omega.RecursiveAddressing

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for spectral definability through the visible quotient.
    thm:prefix-site-spectral-definability-avis -/
theorem paper_recursive_addressing_prefix_site_spectral_definability_avis
    {Character : Type} (dualIdentifiesAnnihilator : Prop) (annihilator : Character → Prop)
    (spectrallyDefinable : Character → Prop)
    (hDual : dualIdentifiesAnnihilator)
    (hDef : ∀ χ, spectrallyDefinable χ ↔ annihilator χ) :
    dualIdentifiesAnnihilator ∧ ∀ χ, spectrallyDefinable χ ↔ annihilator χ := by
  exact ⟨hDual, hDef⟩

end Omega.RecursiveAddressing

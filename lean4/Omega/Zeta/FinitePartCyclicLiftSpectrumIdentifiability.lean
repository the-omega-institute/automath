import Omega.Zeta.IntroCyclicReconstruction

namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for spectral identifiability from cyclic lifts
in the ETDS finite-part section.
    thm:finite-part-cyclic-lift-spectrum-identifiability -/
theorem paper_etds_finite_part_cyclic_lift_spectrum_identifiability
    {Matrix ReducedPoly Spectrum LayerDatum : Type}
    (Psi : Matrix → ℕ → ℝ)
    (F : Matrix → ReducedPoly)
    (nonPerronSpectrum : Matrix → Spectrum)
    (layer : Matrix → ℕ → LayerDatum)
    (determinesReducedPoly : (ℕ → ℝ) → ReducedPoly → Prop)
    (encodesSpectrum : ReducedPoly → Spectrum → Prop)
    (singleLayerDetermines : ℕ → LayerDatum → ReducedPoly → Prop)
    (exponentialFingerprint : (ℕ → ℝ) → Prop)
    {A : Matrix} {d q : ℕ}
    (hdet : determinesReducedPoly (Psi A) (F A))
    (hspec : encodesSpectrum (F A) (nonPerronSpectrum A))
    (hsingle : d ≤ q → singleLayerDetermines q (layer A q) (F A))
    (hexp : exponentialFingerprint (Psi A)) :
    (determinesReducedPoly (Psi A) (F A) ∧
      encodesSpectrum (F A) (nonPerronSpectrum A)) ∧
      exponentialFingerprint (Psi A) := by
  have hIntro :=
    paper_etds_intro_cyclic_reconstruction_package
      Psi F nonPerronSpectrum layer determinesReducedPoly encodesSpectrum
      singleLayerDetermines exponentialFingerprint hdet hspec hsingle hexp
  exact ⟨hIntro.1, hIntro.2.2⟩

/-- Chapter-facing wrapper around the ETDS cyclic-lift spectrum package.
    thm:finite-part-cyclic-lift-spectrum-identifiability -/
theorem paper_finite_part_cyclic_lift_spectrum_identifiability
    {Matrix ReducedPoly Spectrum LayerDatum : Type}
    (Psi : Matrix → ℕ → ℝ)
    (F : Matrix → ReducedPoly)
    (nonPerronSpectrum : Matrix → Spectrum)
    (layer : Matrix → ℕ → LayerDatum)
    (determinesReducedPoly : (ℕ → ℝ) → ReducedPoly → Prop)
    (encodesSpectrum : ReducedPoly → Spectrum → Prop)
    (singleLayerDetermines : ℕ → LayerDatum → ReducedPoly → Prop)
    (exponentialFingerprint : (ℕ → ℝ) → Prop)
    {A : Matrix} {d q : ℕ}
    (hdet : determinesReducedPoly (Psi A) (F A))
    (hspec : encodesSpectrum (F A) (nonPerronSpectrum A))
    (hsingle : d ≤ q → singleLayerDetermines q (layer A q) (F A))
    (hexp : exponentialFingerprint (Psi A)) :
    (determinesReducedPoly (Psi A) (F A) ∧
      encodesSpectrum (F A) (nonPerronSpectrum A)) ∧
      exponentialFingerprint (Psi A) := by
  exact
    paper_etds_finite_part_cyclic_lift_spectrum_identifiability
      Psi F nonPerronSpectrum layer determinesReducedPoly encodesSpectrum
      singleLayerDetermines exponentialFingerprint hdet hspec hsingle hexp

end Omega.Zeta

import Mathlib.Tactic

namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Paper-facing seed for the ETDS introduction theorem on cyclic reconstruction.  The three
conclusions are packaged as: determination of the reduced polynomial from the cyclic fingerprint,
recovery from a single root-of-unity layer once `q ≥ d`, and the exponential-fingerprint formula.
    thm:intro-cyclic-reconstruction -/
theorem paper_etds_intro_cyclic_reconstruction_seeds
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
    (d ≤ q → singleLayerDetermines q (layer A q) (F A)) ∧
    exponentialFingerprint (Psi A) := by
  exact ⟨⟨hdet, hspec⟩, hsingle, hexp⟩

set_option maxHeartbeats 400000 in
/-- Packaged form of the introduction-level cyclic reconstruction seed.
    thm:intro-cyclic-reconstruction -/
theorem paper_etds_intro_cyclic_reconstruction_package
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
    (d ≤ q → singleLayerDetermines q (layer A q) (F A)) ∧
    exponentialFingerprint (Psi A) :=
  paper_etds_intro_cyclic_reconstruction_seeds
    Psi F nonPerronSpectrum layer determinesReducedPoly encodesSpectrum
    singleLayerDetermines exponentialFingerprint hdet hspec hsingle hexp

end Omega.Zeta

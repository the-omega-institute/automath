import Omega.Zeta.FinitePartSingleQTorsionReconstruction

namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the single-layer square-root test corollary.
    cor:finite-part-single-layer-square-root-test -/
theorem paper_etds_finite_part_single_layer_square_root_test
    {Matrix ReducedPoly Spectrum LayerDatum : Type}
    (Psi : Matrix → ℕ → ℝ)
    (F : Matrix → ReducedPoly)
    (nonPerronSpectrum : Matrix → Spectrum)
    (layer : Matrix → ℕ → LayerDatum)
    (determinesReducedPoly : (ℕ → ℝ) → ReducedPoly → Prop)
    (encodesSpectrum : ReducedPoly → Spectrum → Prop)
    (singleLayerDetermines : ℕ → LayerDatum → ReducedPoly → Prop)
    (exponentialFingerprint : (ℕ → ℝ) → Prop)
    (passesSquareRootTest : ℕ → LayerDatum → Prop)
    (squareRootBound : Spectrum → Prop)
    {A : Matrix} {d q : ℕ}
    (hdet : determinesReducedPoly (Psi A) (F A))
    (hspec : encodesSpectrum (F A) (nonPerronSpectrum A))
    (hsingle : d ≤ q → singleLayerDetermines q (layer A q) (F A))
    (hexp : exponentialFingerprint (Psi A))
    (htest : ∀ {G : ReducedPoly} {S : Spectrum},
      singleLayerDetermines q (layer A q) G →
      encodesSpectrum G S →
      (passesSquareRootTest q (layer A q) ↔ squareRootBound S))
    (hq : d ≤ q) :
    passesSquareRootTest q (layer A q) ↔ squareRootBound (nonPerronSpectrum A) := by
  have hsingleLayer :
      singleLayerDetermines q (layer A q) (F A) :=
    paper_etds_finite_part_single_q_torsion_reconstruction
      Psi F nonPerronSpectrum layer determinesReducedPoly encodesSpectrum
      singleLayerDetermines exponentialFingerprint hdet hspec hsingle hexp hq
  exact htest hsingleLayer hspec

end Omega.Zeta

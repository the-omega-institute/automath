import Omega.Zeta.FinitePartSingleQTorsionReconstruction

namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for reconstruction from a single `q`-torsion layer in the
finite-part cyclic-lift section.
    thm:finite-part-cyclic-lift-single-q-torsion-reconstruction -/
theorem paper_finite_part_cyclic_lift_single_q_torsion_reconstruction
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
    (hexp : exponentialFingerprint (Psi A))
    (hq : d ≤ q) :
    singleLayerDetermines q (layer A q) (F A) := by
  exact
    paper_etds_finite_part_single_q_torsion_reconstruction
      Psi F nonPerronSpectrum layer determinesReducedPoly encodesSpectrum
      singleLayerDetermines exponentialFingerprint hdet hspec hsingle hexp hq

end Omega.Zeta

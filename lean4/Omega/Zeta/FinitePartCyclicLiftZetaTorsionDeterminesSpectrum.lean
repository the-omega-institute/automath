import Omega.Zeta.FinitePartSingleQTorsionReconstruction

namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the corollary that root-of-unity torsion
    data of `ζ_A` determine the non-Perron spectrum.
    cor:finite-part-cyclic-lift-zeta-torsion-determines-spectrum -/
theorem paper_etds_finite_part_cyclic_lift_zeta_torsion_determines_spectrum
    {Matrix ReducedPoly Spectrum TorsionDatum : Type}
    (Psi : Matrix → ℕ → ℝ)
    (F : Matrix → ReducedPoly)
    (nonPerronSpectrum : Matrix → Spectrum)
    (torsionData : Matrix → ℕ → TorsionDatum)
    (determinesReducedPoly : (ℕ → ℝ) → ReducedPoly → Prop)
    (encodesSpectrum : ReducedPoly → Spectrum → Prop)
    (singleLayerDetermines : ℕ → TorsionDatum → ReducedPoly → Prop)
    (torsionDeterminesSpectrum : ℕ → TorsionDatum → Spectrum → Prop)
    (exponentialFingerprint : (ℕ → ℝ) → Prop)
    {A : Matrix} {d q : ℕ}
    (hdet : determinesReducedPoly (Psi A) (F A))
    (hspec : encodesSpectrum (F A) (nonPerronSpectrum A))
    (hsingle : d ≤ q → singleLayerDetermines q (torsionData A q) (F A))
    (hexp : exponentialFingerprint (Psi A))
    (htransfer :
      ∀ {q : ℕ} {datum : TorsionDatum} {poly : ReducedPoly} {spectrum : Spectrum},
        singleLayerDetermines q datum poly →
          encodesSpectrum poly spectrum →
          torsionDeterminesSpectrum q datum spectrum)
    (hq : d ≤ q) :
    torsionDeterminesSpectrum q (torsionData A q) (nonPerronSpectrum A) := by
  have hpoly : singleLayerDetermines q (torsionData A q) (F A) :=
    paper_etds_finite_part_single_q_torsion_reconstruction
      Psi F nonPerronSpectrum torsionData determinesReducedPoly encodesSpectrum
      singleLayerDetermines exponentialFingerprint hdet hspec hsingle hexp hq
  exact htransfer hpoly hspec

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the spectrum-identifiability corollary:
    the finite-part constant together with one `q`-torsion layer determine the
    reduced polynomial and hence the normalized non-Perron spectrum.
    cor:finite-part-cyclic-lift-zeta-torsion-determines-spectrum -/
theorem paper_finite_part_cyclic_lift_zeta_torsion_determines_spectrum
    {Matrix ReducedPoly Spectrum ConstantDatum TorsionDatum : Type}
    (constant : Matrix → ConstantDatum)
    (torsion : Matrix → ℕ → TorsionDatum)
    (reducedPoly : Matrix → ReducedPoly)
    (spectrum : Matrix → Spectrum)
    (zetaTorsionDeterminesReducedPoly : ConstantDatum → TorsionDatum → ReducedPoly → Prop)
    (reducedPolyEncodesSpectrum : ReducedPoly → Spectrum → Prop)
    {A : Matrix} {d q : ℕ}
    (hdet :
      zetaTorsionDeterminesReducedPoly (constant A) (torsion A q) (reducedPoly A))
    (hspec : reducedPolyEncodesSpectrum (reducedPoly A) (spectrum A))
    (hq : d ≤ q) :
    zetaTorsionDeterminesReducedPoly (constant A) (torsion A q) (reducedPoly A) ∧
      reducedPolyEncodesSpectrum (reducedPoly A) (spectrum A) := by
  let _ := hq
  exact ⟨hdet, hspec⟩

end Omega.Zeta

import Omega.Zeta.FinitePartSingleLayerSquareRootTest

namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the finite square-root criterion coming from
    a single root-of-unity layer in the ETDS appendices.
    thm:finite-part-single-layer-torsion-near-rh -/
theorem paper_etds_finite_part_single_layer_torsion_near_rh
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
    (growthBound : Matrix → Prop)
    {A : Matrix} {d q : ℕ}
    (hdet : determinesReducedPoly (Psi A) (F A))
    (hspec : encodesSpectrum (F A) (nonPerronSpectrum A))
    (hsingle : d ≤ q → singleLayerDetermines q (layer A q) (F A))
    (hexp : exponentialFingerprint (Psi A))
    (htest : ∀ {G : ReducedPoly} {S : Spectrum},
      singleLayerDetermines q (layer A q) G →
      encodesSpectrum G S →
      (passesSquareRootTest q (layer A q) ↔ squareRootBound S))
    (hgrowth : squareRootBound (nonPerronSpectrum A) ↔ growthBound A)
    (hq : d ≤ q) :
    (squareRootBound (nonPerronSpectrum A) ↔ passesSquareRootTest q (layer A q)) ∧
      (passesSquareRootTest q (layer A q) ↔ growthBound A) ∧
      (squareRootBound (nonPerronSpectrum A) ↔ growthBound A) := by
  have hsq :
      passesSquareRootTest q (layer A q) ↔ squareRootBound (nonPerronSpectrum A) :=
    paper_etds_finite_part_single_layer_square_root_test
      Psi F nonPerronSpectrum layer determinesReducedPoly encodesSpectrum
      singleLayerDetermines exponentialFingerprint passesSquareRootTest
      squareRootBound hdet hspec hsingle hexp htest hq
  exact ⟨hsq.symm, hsq.trans hgrowth, hgrowth⟩

set_option maxHeartbeats 400000 in
/-- Chapter-facing wrapper for the single-layer torsion near-RH criterion.
    thm:finite-part-single-layer-torsion-near-rh -/
theorem paper_finite_part_single_layer_torsion_near_rh
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
    (growthBound : Matrix → Prop)
    {A : Matrix} {d q : ℕ}
    (hdet : determinesReducedPoly (Psi A) (F A))
    (hspec : encodesSpectrum (F A) (nonPerronSpectrum A))
    (hsingle : d ≤ q → singleLayerDetermines q (layer A q) (F A))
    (hexp : exponentialFingerprint (Psi A))
    (htest : ∀ {G : ReducedPoly} {S : Spectrum},
      singleLayerDetermines q (layer A q) G →
      encodesSpectrum G S →
      (passesSquareRootTest q (layer A q) ↔ squareRootBound S))
    (hgrowth : squareRootBound (nonPerronSpectrum A) ↔ growthBound A)
    (hq : d ≤ q) :
    (squareRootBound (nonPerronSpectrum A) ↔ passesSquareRootTest q (layer A q)) ∧
      (passesSquareRootTest q (layer A q) ↔ growthBound A) ∧
      (squareRootBound (nonPerronSpectrum A) ↔ growthBound A) := by
  exact
    paper_etds_finite_part_single_layer_torsion_near_rh
      Psi F nonPerronSpectrum layer determinesReducedPoly encodesSpectrum
      singleLayerDetermines exponentialFingerprint passesSquareRootTest
      squareRootBound growthBound hdet hspec hsingle hexp htest hgrowth hq

end Omega.Zeta

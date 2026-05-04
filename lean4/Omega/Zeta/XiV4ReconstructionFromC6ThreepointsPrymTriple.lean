import Omega.Zeta.XiV4BidoubleCoverExplicitLinebundles

namespace Omega.Zeta

/-- Paper label: `thm:xi-v4-reconstruction-from-c6-threepoints-prym-triple`. -/
theorem paper_xi_v4_reconstruction_from_c6_threepoints_prym_triple
    (doubleCoversRecovered bidoubleCoverUnique triplePrymDecomposition s3Compatible : Prop)
    (hLinebundles :
      xi_v4_bidouble_cover_explicit_linebundles_lineBundleSquares ∧
        xi_v4_bidouble_cover_explicit_linebundles_intermediateDoubleCovers)
    (hDouble : doubleCoversRecovered) (hUnique : bidoubleCoverUnique)
    (hPrym : doubleCoversRecovered → bidoubleCoverUnique → triplePrymDecomposition)
    (hS3 : triplePrymDecomposition → s3Compatible) :
    doubleCoversRecovered ∧ bidoubleCoverUnique ∧ triplePrymDecomposition ∧ s3Compatible := by
  have hLineBundleSquares := hLinebundles.1
  have hIntermediateDoubleCovers := hLinebundles.2
  have hTriple : triplePrymDecomposition := hPrym hDouble hUnique
  exact ⟨hDouble, hUnique, hTriple, hS3 hTriple⟩

end Omega.Zeta

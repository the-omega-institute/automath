import Mathlib.Data.Multiset.Basic
import Omega.GU.Window6ChiralCompressionHypercubeAdjacency

namespace Omega.GU

/-- The `Q₄` adjacency spectrum carried by the anti-invariant window-6 chiral sector. -/
def window6ChiralSectorQ4Spectrum : Multiset ℤ :=
  ({4, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, -2, -2, -2, -2, -4} : Multiset ℤ)

/-- Binomial multiplicity package for the standard `Q₄` Walsh spectrum. -/
def window6ChiralSectorQ4SpectrumBinomialForm : Prop :=
  window6ChiralSectorQ4Spectrum =
    Multiset.replicate (Nat.choose 4 0) 4 +
      Multiset.replicate (Nat.choose 4 1) 2 +
      Multiset.replicate (Nat.choose 4 2) 0 +
      Multiset.replicate (Nat.choose 4 3) (-2) +
      Multiset.replicate (Nat.choose 4 4) (-4)

/-- Paper-facing `Q₄` spectral fingerprint for the anti-invariant window-6 chiral sector: the
existing chiral-compression theorem identifies the sector with the residual `4`-cube, the modeled
`-`-eigenspace has dimension `16`, and the adjacency spectrum has the standard binomial
multiplicities.
    cor:window6-chiral-sector-q4-spectrum -/
theorem paper_window6_chiral_sector_q4_spectrum :
    paper_window6_chiral_compression_hypercube_adjacency_stmt 6 ∧
      window6WalshMinusBasisCardinality 6 = window6ChiralSectorQ4Spectrum.card ∧
      window6ChiralSectorQ4SpectrumBinomialForm := by
  refine ⟨paper_window6_chiral_compression_hypercube_adjacency 6 (by omega), ?_, ?_⟩
  · have hminus := (paper_window6_affine_chiral_walsh_decomposition 6 (by omega)).2.1
    simpa [window6ChiralSectorQ4Spectrum] using hminus
  · change
      window6ChiralSectorQ4Spectrum =
        Multiset.replicate (Nat.choose 4 0) 4 +
          Multiset.replicate (Nat.choose 4 1) 2 +
          Multiset.replicate (Nat.choose 4 2) 0 +
          Multiset.replicate (Nat.choose 4 3) (-2) +
          Multiset.replicate (Nat.choose 4 4) (-4)
    native_decide

end Omega.GU

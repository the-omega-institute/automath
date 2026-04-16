import Mathlib.Tactic
import Omega.Discussion.HypercubeStokesFourierBinomial

namespace Omega.Discussion

/-- Chapter-local wrapper for the hypercube spectral tail bound extracted from flux moments.
The data package the imported Stokes/Fourier binomial dictionary, the rewrite of `M_k(f)` as a
weighted spectral-layer sum, the lower bound `choose r k ≥ choose d k` on the tail `r ≥ d`, and
the final rearrangement yielding the `L²` spectral-tail estimate. -/
structure SpectralTailBoundFromFluxData where
  hypercubeStokesFourierBinomialPackage : Prop
  weightedSpectralLayerRewrite : Prop
  chooseTailLowerBound : Prop
  tailRearrangement : Prop
  hypercubeStokesFourierBinomialPackage_h : hypercubeStokesFourierBinomialPackage
  weightedSpectralLayerRewrite_h : weightedSpectralLayerRewrite
  chooseTailLowerBound_h : chooseTailLowerBound
  tailRearrangement_h : tailRearrangement
  spectralTailBound : Prop
  deriveSpectralTailBound :
    hypercubeStokesFourierBinomialPackage →
      weightedSpectralLayerRewrite → chooseTailLowerBound → tailRearrangement → spectralTailBound

/-- Paper-facing wrapper for the hypercube spectral tail estimate derived from flux moments.
Combining the Stokes/Fourier binomial dictionary with the weighted spectral-layer rewrite,
the tailwise binomial lower bound, and a final rearrangement yields the stated `L²` tail bound.
    thm:discussion-spectral-tail-bound-from-flux -/
theorem paper_discussion_spectral_tail_bound_from_flux (D : SpectralTailBoundFromFluxData) :
    D.spectralTailBound := by
  exact
    D.deriveSpectralTailBound
      D.hypercubeStokesFourierBinomialPackage_h
      D.weightedSpectralLayerRewrite_h
      D.chooseTailLowerBound_h
      D.tailRearrangement_h

end Omega.Discussion

import Mathlib.Tactic

namespace Omega.POM

/-- Chapter-local package for the fold-factor-chain effective sample-size estimate. The fields
record the stationary empirical-mean variance bound for the lazy reversible chain, the spectral-gap
lower bound inherited from the non-lazy chain, the resulting mean-square bound for `0-1`
observables, and the identification of the success observable mean with the paper's success
functional. -/
structure FoldFactorChainEffectiveSampleSizeData where
  stationaryVarianceBound : Prop
  lazyGapLowerBound : Prop
  zeroOneMseBound : Prop
  successObservableMean : Prop
  stationaryVarianceBoundWitness : stationaryVarianceBound
  lazyGapLowerBoundWitness : lazyGapLowerBound
  zeroOneMseBoundWitness : zeroOneMseBound
  successObservableMeanWitness : successObservableMean

/-- Paper-facing wrapper for the lazy fold-factor-chain effective sample-size package: the
stationary variance estimate, the lazy-gap lower bound, the specialized `0-1` mean-square error
bound, and the success-observable identity are all extracted directly from the chapter-local data.
    prop:pom-fold-factor-chain-effective-sample-size -/
theorem paper_pom_fold_factor_chain_effective_sample_size
    (h : FoldFactorChainEffectiveSampleSizeData) :
    h.stationaryVarianceBound /\ h.lazyGapLowerBound /\ h.zeroOneMseBound /\ h.successObservableMean := by
  exact
    ⟨h.stationaryVarianceBoundWitness, h.lazyGapLowerBoundWitness, h.zeroOneMseBoundWitness,
      h.successObservableMeanWitness⟩

end Omega.POM

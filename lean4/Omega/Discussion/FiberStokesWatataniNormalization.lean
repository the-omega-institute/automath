import Omega.Discussion.HypercubeStokesFourierBinomial

namespace Omega.Discussion

/-- Paper-facing wrapper for the fiberwise Stokes/Watatani normalization package: the conditional
parity expectation is rewritten as a signed fiber count, bounded by total boundary flux, and then
normalized by the Watatani-index multiplicity field.
    prop:discussion-fiber-stokes-watatani-normalization -/
theorem paper_discussion_fiber_stokes_watatani_normalization
    (fiberExpectationFormula fiberBiasBound watataniIndexNormalization : Prop)
    (hExp : fiberExpectationFormula)
    (hBound : fiberBiasBound)
    (hNorm : watataniIndexNormalization) :
    fiberExpectationFormula ∧ fiberBiasBound ∧ watataniIndexNormalization := by
  exact ⟨hExp, hBound, hNorm⟩

end Omega.Discussion

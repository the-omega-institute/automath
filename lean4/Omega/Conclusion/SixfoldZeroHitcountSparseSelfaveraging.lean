import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `prop:conclusion-sixfold-zero-hitcount-sparse-selfaveraging`. -/
theorem paper_conclusion_sixfold_zero_hitcount_sparse_selfaveraging
    (sparsePhase selfAveragingPhase : Prop) (hSparse : sparsePhase)
    (hSelf : selfAveragingPhase) :
    sparsePhase ∧ selfAveragingPhase := by
  exact ⟨hSparse, hSelf⟩

end Omega.Conclusion

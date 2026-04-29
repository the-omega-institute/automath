import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-zg-positive-entropy-finitestate-obstruction`. -/
theorem paper_conclusion_zg_positive_entropy_finitestate_obstruction {Source Measure : Type*}
    (push : Source → Measure) (muB : Measure) (positiveEntropyFiniteState : Source → Prop)
    (positiveLocalDimensionAE exactDimensionZeroAE : Measure → Prop)
    (hSMB : ∀ ν, positiveEntropyFiniteState ν → positiveLocalDimensionAE (push ν))
    (hMuBZero : exactDimensionZeroAE muB)
    (hIncompatible : ∀ μ, positiveLocalDimensionAE μ → exactDimensionZeroAE μ → False) :
    ∀ ν, positiveEntropyFiniteState ν → push ν ≠ muB := by
  intro ν hν hpush
  exact hIncompatible (push ν) (hSMB ν hν) (hpush.symm ▸ hMuBZero)

end Omega.Conclusion

import Mathlib.Logic.Basic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-binfold-divergence-cone-observable-rank-one`. -/
theorem paper_conclusion_binfold_divergence_cone_observable_rank_one
    (twoPointFactorization quotientFactorization singleScalarObservable : Prop)
    (hTwo : twoPointFactorization) (hQuot : quotientFactorization)
    (hSingle : singleScalarObservable) :
    twoPointFactorization ∧ quotientFactorization ∧ singleScalarObservable := by
  exact ⟨hTwo, hQuot, hSingle⟩

end Omega.Conclusion

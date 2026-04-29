import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `prop:conclusion-prime-adjunction-no-finite-rank-additive-linearization`. -/
theorem paper_conclusion_prime_adjunction_no_finite_rank_additive_linearization
    (finiteRankTarget exactLinearizesMissingPrimeMonoid : Prop)
    (rankObstruction : exactLinearizesMissingPrimeMonoid → False) :
    ¬ (finiteRankTarget ∧ exactLinearizesMissingPrimeMonoid) := by
  intro h
  exact rankObstruction h.2

end Omega.Conclusion

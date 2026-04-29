import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-prime-log-infinite-rank-register`. -/
theorem paper_conclusion_prime_log_infinite_rank_register {Route Factor : Type*}
    (finiteVisible : Factor → Prop) (factorsThrough : Route → Factor → Prop)
    (exactPrimeLogBoundary : Route → Prop) (route : Route)
    (hExactForcesNoFinite :
      exactPrimeLogBoundary route → ∀ F, finiteVisible F → ¬ factorsThrough route F)
    (hExact : exactPrimeLogBoundary route) :
    ∀ F, finiteVisible F → ¬ factorsThrough route F := by
  exact hExactForcesNoFinite hExact

end Omega.Conclusion

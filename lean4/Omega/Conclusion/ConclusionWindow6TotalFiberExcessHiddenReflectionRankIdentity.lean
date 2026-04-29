import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label:
`thm:conclusion-window6-total-fiber-excess-hidden-reflection-rank-identity`. -/
theorem paper_conclusion_window6_total_fiber_excess_hidden_reflection_rank_identity
    (fiberExcess hiddenRank : Nat)
    (hfiber : fiberExcess = 43)
    (hrank : hiddenRank = 8 * 1 + 4 * 2 + 9 * 3) :
    fiberExcess = hiddenRank /\ 64 = 21 + hiddenRank := by
  subst fiberExcess
  subst hiddenRank
  norm_num

end Omega.Conclusion

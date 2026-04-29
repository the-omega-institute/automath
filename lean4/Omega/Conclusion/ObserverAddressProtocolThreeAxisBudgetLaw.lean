import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-observer-address-protocol-three-axis-budget-law`. -/
theorem paper_conclusion_observer_address_protocol_three_axis_budget_law
    (cardR cardH : ℕ) (fail timeTerm collisionTerm eta : ℝ) (hCard : cardH ≤ cardR)
    (hFail : fail ≤ timeTerm + collisionTerm) (hTime : timeTerm ≤ eta / 2)
    (hCollision : collisionTerm ≤ eta / 2) : cardH ≤ cardR ∧ fail ≤ eta := by
  refine ⟨hCard, ?_⟩
  calc
    fail ≤ timeTerm + collisionTerm := hFail
    _ ≤ eta / 2 + eta / 2 := add_le_add hTime hCollision
    _ = eta := by ring

end Omega.Conclusion

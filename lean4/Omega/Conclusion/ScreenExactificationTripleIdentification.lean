import Mathlib.Data.Nat.Basic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-screen-exactification-triple-identification`.

The three screen exactification quantities are identified by combining the previously established
cost, corank, and minimal-addition equalities. -/
theorem paper_conclusion_screen_exactification_triple_identification
    (rho rank componentCount auditCost minAdded : ℕ)
    (hCost : auditCost = componentCount - 1) (hRank : auditCost = rho - rank)
    (hMin : minAdded = componentCount - 1) :
    auditCost = componentCount - 1 ∧ auditCost = rho - rank ∧ minAdded = auditCost := by
  exact ⟨hCost, hRank, hMin.trans hCost.symm⟩

end Omega.Conclusion

import Omega.Conclusion.ScreenVisibleExternalAuditConservation

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-screen-visible-hidden-padic-entropy-conservation`.
Replacing the hidden fiber entropy by the external audit cost gives the same cardinality/rank
conservation law, its ambient-rank lower bound, and the equality criterion for independence. -/
theorem paper_conclusion_screen_visible_hidden_padic_entropy_conservation
    (D : conclusion_screen_visible_external_audit_conservation_Data) (fiberEntropy : ℕ)
    (hFiber : fiberEntropy = D.auditCost) :
    D.screen.card + fiberEntropy = D.ambientRank + (D.screen.card - D.screenRank) ∧
    D.ambientRank ≤ D.screen.card + fiberEntropy ∧
    (D.screen.card + fiberEntropy = D.ambientRank ↔ D.independent) := by
  have hVisible : D.screenRank ≤ D.screen.card := D.hScreenRankLeVisible
  have hAmbient : D.screenRank ≤ D.ambientRank := D.hScreenRankLeAmbient
  rw [hFiber, D.hAuditCost]
  constructor
  · omega
  constructor
  · omega
  · rw [conclusion_screen_visible_external_audit_conservation_Data.independent]
    constructor <;> intro h <;> omega

end Omega.Conclusion

import Mathlib

namespace Omega.Conclusion

/-- Concrete rank-and-audit data for a visible screen inside a finite ambient rank. -/
structure conclusion_screen_visible_external_audit_conservation_Data where
  ambientRank : ℕ
  screen : Finset ℕ
  screenRank : ℕ
  auditCost : ℕ
  hAuditCost : auditCost = ambientRank - screenRank
  hScreenRankLeVisible : screenRank ≤ screen.card
  hScreenRankLeAmbient : screenRank ≤ ambientRank

namespace conclusion_screen_visible_external_audit_conservation_Data

/-- Independence is the usual equality between screen cardinality and its rank. -/
def independent (D : conclusion_screen_visible_external_audit_conservation_Data) : Prop :=
  D.screenRank = D.screen.card

/-- A basis screen has full ambient rank. -/
def basis (D : conclusion_screen_visible_external_audit_conservation_Data) : Prop :=
  D.screenRank = D.ambientRank

/-- The external audit cost is the ambient corank. -/
def auditCostFormula (D : conclusion_screen_visible_external_audit_conservation_Data) : Prop :=
  D.auditCost = D.ambientRank - D.screenRank

/-- Visible coordinates plus external audit never cost less than ambient rank. -/
def totalCostLowerBound (D : conclusion_screen_visible_external_audit_conservation_Data) : Prop :=
  D.screen.card + D.auditCost ≥ D.ambientRank

/-- Equality in the lower bound is equivalent to independence. -/
def equalityIffIndependent (D : conclusion_screen_visible_external_audit_conservation_Data) :
    Prop :=
  D.screen.card + D.auditCost = D.ambientRank ↔ D.independent

/-- Zero external audit is equivalent to full-rank visibility. -/
def zeroAuditIffBasis (D : conclusion_screen_visible_external_audit_conservation_Data) : Prop :=
  D.auditCost = 0 ↔ D.basis

end conclusion_screen_visible_external_audit_conservation_Data

/-- Paper label: `thm:conclusion-screen-visible-external-audit-conservation`.
The audit identity `a(S) = rho - r(S)` gives the rank lower bound; equality is exactly
`r(S) = |S|`, and zero audit is exactly full ambient rank. -/
theorem paper_conclusion_screen_visible_external_audit_conservation
    (D : conclusion_screen_visible_external_audit_conservation_Data) :
    D.auditCostFormula ∧ D.totalCostLowerBound ∧ D.equalityIffIndependent ∧
      D.zeroAuditIffBasis := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact D.hAuditCost
  · rw [conclusion_screen_visible_external_audit_conservation_Data.totalCostLowerBound,
      D.hAuditCost]
    have hVisible : D.screenRank ≤ D.screen.card := D.hScreenRankLeVisible
    have hAmbient : D.screenRank ≤ D.ambientRank := D.hScreenRankLeAmbient
    omega
  · rw [conclusion_screen_visible_external_audit_conservation_Data.equalityIffIndependent,
      conclusion_screen_visible_external_audit_conservation_Data.independent, D.hAuditCost]
    have hVisible : D.screenRank ≤ D.screen.card := D.hScreenRankLeVisible
    have hAmbient : D.screenRank ≤ D.ambientRank := D.hScreenRankLeAmbient
    constructor <;> intro h <;> omega
  · rw [conclusion_screen_visible_external_audit_conservation_Data.zeroAuditIffBasis,
      conclusion_screen_visible_external_audit_conservation_Data.basis, D.hAuditCost]
    have hAmbient : D.screenRank ≤ D.ambientRank := D.hScreenRankLeAmbient
    constructor <;> intro h <;> omega

end Omega.Conclusion

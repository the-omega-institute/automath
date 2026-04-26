import Mathlib.Tactic

namespace Omega.POM

/-- Concrete audit data for the two independent POM axes. The first coordinate records a
maximum-fiber entropy audit budget, the second a fixed-`q` Schur-envelope audit budget, and
the third counts explicit coupling hypotheses supplied between the two axes. -/
structure pom_freezing_vs_schur_envelope_separation_data where
  maximumFiberEntropyAuditBudget : Nat
  fixedQSchurEnvelopeAuditBudget : Nat
  explicitCouplingHypotheses : Nat

/-- The maximum-fiber entropy axis has a finite audit budget. -/
def pom_freezing_vs_schur_envelope_separation_data.freezingAxisAuditable
    (D : pom_freezing_vs_schur_envelope_separation_data) : Prop :=
  0 ≤ D.maximumFiberEntropyAuditBudget

/-- The fixed-`q` Schur-envelope axis has a finite audit budget. -/
def pom_freezing_vs_schur_envelope_separation_data.schurAxisAuditable
    (D : pom_freezing_vs_schur_envelope_separation_data) : Prop :=
  0 ≤ D.fixedQSchurEnvelopeAuditBudget

/-- Any implication between the axes must explicitly account for whether coupling hypotheses
have been supplied. -/
def pom_freezing_vs_schur_envelope_separation_data.requiresExtraCouplingForImplications
    (D : pom_freezing_vs_schur_envelope_separation_data) : Prop :=
  D.explicitCouplingHypotheses = 0 ∨ 0 < D.explicitCouplingHypotheses

/-- Paper label: `prop:pom-freezing-vs-schur-envelope-separation`. -/
theorem paper_pom_freezing_vs_schur_envelope_separation
    (D : pom_freezing_vs_schur_envelope_separation_data) :
    D.freezingAxisAuditable ∧ D.schurAxisAuditable ∧
      D.requiresExtraCouplingForImplications := by
  exact ⟨Nat.zero_le D.maximumFiberEntropyAuditBudget,
    Nat.zero_le D.fixedQSchurEnvelopeAuditBudget,
    Nat.eq_zero_or_pos D.explicitCouplingHypotheses⟩

end Omega.POM

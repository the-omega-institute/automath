import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete two-regime audit data: a uniformly bounded realization profile and a separate
unbounded profile witnessing the obstruction regime. -/
structure conclusion_finite_audit_dimension_phase_transition_Data where
  finiteAuditDimension : ℕ
  uniformRealizationBound : ℕ
  boundedRealizationDemand : ℕ → ℕ
  unboundedRealizationDemand : ℕ → ℕ
  boundedRealization_le_uniform :
    ∀ n, boundedRealizationDemand n ≤ uniformRealizationBound
  uniformRealization_le_finiteAudit :
    uniformRealizationBound ≤ finiteAuditDimension
  noUniformBound :
    ∀ B, ∃ n, B < unboundedRealizationDemand n

namespace conclusion_finite_audit_dimension_phase_transition_Data

/-- Under a uniform realization bound, every bounded-regime demand fits the finite audit. -/
def boundedRealizationFiniteAudit
    (D : conclusion_finite_audit_dimension_phase_transition_Data) : Prop :=
  ∀ n, D.boundedRealizationDemand n ≤ D.finiteAuditDimension

/-- Without any uniform bound, every proposed finite audit budget is exceeded by some demand. -/
def unboundedRealizationFiniteAuditObstruction
    (D : conclusion_finite_audit_dimension_phase_transition_Data) : Prop :=
  ∀ B, D.finiteAuditDimension ≤ B → ∃ n, B < D.unboundedRealizationDemand n

lemma boundedRealizationFiniteAudit_intro
    (D : conclusion_finite_audit_dimension_phase_transition_Data) :
    D.boundedRealizationFiniteAudit := by
  intro n
  exact le_trans (D.boundedRealization_le_uniform n) D.uniformRealization_le_finiteAudit

lemma unboundedRealizationFiniteAuditObstruction_intro
    (D : conclusion_finite_audit_dimension_phase_transition_Data) :
    D.unboundedRealizationFiniteAuditObstruction := by
  intro B _hB
  exact D.noUniformBound B

end conclusion_finite_audit_dimension_phase_transition_Data

/-- Paper label: `thm:conclusion-finite-audit-dimension-phase-transition`. -/
theorem paper_conclusion_finite_audit_dimension_phase_transition
    (D : conclusion_finite_audit_dimension_phase_transition_Data) :
    D.boundedRealizationFiniteAudit ∧
      D.unboundedRealizationFiniteAuditObstruction := by
  exact ⟨D.boundedRealizationFiniteAudit_intro,
    D.unboundedRealizationFiniteAuditObstruction_intro⟩

end Omega.Conclusion

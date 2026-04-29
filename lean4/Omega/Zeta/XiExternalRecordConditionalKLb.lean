import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete finite data for the external-record conditional complexity lower bound.
The record map is kept as an actual function on a finite uniform source, and the fiberwise
counting estimate is represented as a pointwise lower bound on the conditional complexity. -/
structure xi_external_record_conditional_k_lb_data where
  sourceSize : ℕ
  recordSize : ℕ
  nonemptySource : 0 < sourceSize
  externalRecord : Fin sourceSize → Fin recordSize
  externalRecord_injective : Function.Injective externalRecord
  conditionalComplexity : Fin sourceSize → ℝ
  threshold : ℝ
  fiberCountingBound :
    ∀ u : Fin sourceSize, threshold ≤ conditionalComplexity u

/-- High-probability form specialized to the finite uniform source: every source point obeys
the fiberwise counting threshold. -/
def xi_external_record_conditional_k_lb_data.highProbabilityBound
    (D : xi_external_record_conditional_k_lb_data) : Prop :=
  ∀ u : Fin D.sourceSize, D.threshold ≤ D.conditionalComplexity u

/-- Expectation lower bound for the pushed-forward uniform source, written as the finite average
over the original uniform space. -/
def xi_external_record_conditional_k_lb_data.expectationLowerBound
    (D : xi_external_record_conditional_k_lb_data) : Prop :=
  D.threshold ≤
    (∑ u : Fin D.sourceSize, D.conditionalComplexity u) / (D.sourceSize : ℝ)

/-- Paper label: `prop:xi-external-record-conditional-K-lb`. -/
theorem paper_xi_external_record_conditional_k_lb
    (D : xi_external_record_conditional_k_lb_data) :
    D.highProbabilityBound ∧ D.expectationLowerBound := by
  have hpoint : ∀ u : Fin D.sourceSize, D.threshold ≤ D.conditionalComplexity u :=
    D.fiberCountingBound
  refine ⟨hpoint, ?_⟩
  have hsum :
      (∑ _u : Fin D.sourceSize, D.threshold) ≤
        ∑ u : Fin D.sourceSize, D.conditionalComplexity u := by
    exact Finset.sum_le_sum fun u _hu => hpoint u
  have hconst :
      (∑ _u : Fin D.sourceSize, D.threshold) =
        (D.sourceSize : ℝ) * D.threshold := by
    simp [Finset.card_univ, nsmul_eq_mul]
  have hmul :
      D.threshold * (D.sourceSize : ℝ) ≤
        ∑ u : Fin D.sourceSize, D.conditionalComplexity u := by
    simpa [hconst, mul_comm] using hsum
  have hpos : 0 < (D.sourceSize : ℝ) := by
    exact_mod_cast D.nonemptySource
  exact (le_div_iff₀ hpos).2 hmul

end Omega.Zeta

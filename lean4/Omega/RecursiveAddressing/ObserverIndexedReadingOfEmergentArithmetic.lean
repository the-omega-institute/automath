import Omega.RecursiveAddressing.ObserverIndexedFiniteResolutionObjectEligibility
import Omega.RecursiveAddressing.ObserverIndexedValuePreservingNoCreation

namespace Omega.RecursiveAddressing

open FocusedNonNullReadoutCriterion

set_option maxHeartbeats 400000 in
/-- Paper-facing Section 7 reading: emergent arithmetic only acts on address/value pairs that
have already been objectified by the observer-indexed readout layer. Concretely, arithmetic
eligibility supplies a non-`NULL` typed readout, the non-`NULL` criterion exposes the underlying
admissible address together with its witness fiber, fold-equivalent microstates share the same
eligibility class, and value-preserving rewrites cannot create a fresh object-level value out of
an undefined term. Equivalently, fold-equivalent microstates have the same arithmetic
eligibility, and value-preserving rewrites cannot create a value from an undefined source.
    cor:observer-indexed-reading-of-emergent-arithmetic -/
theorem paper_recursive_addressing_observer_indexed_reading_of_emergent_arithmetic
    {Micro State Object Ref Value Expr : Type} [DecidableEq Value]
    (Fold : Micro → Object)
    (address : Object → Ref)
    (Adm : State → Set Ref)
    (Vis Γ : State → Ref → Set Value)
    (hΓ : ∀ p r, Γ p r = {v | Vis p r = {v}})
    (readout : State → Expr → Option Value)
    (step : Expr → Expr → Prop)
    (hpres : ∀ {p t t' v}, step t t' → readout p t' = some v → readout p t = some v)
    {p : State} {ω ω' : Micro} :
    Fold ω = Fold ω' →
      (FiniteResolutionArithmeticEligible Fold address Adm Vis p ω ↔
          FiniteResolutionArithmeticEligible Fold address Adm Vis p ω') ∧
        (∀ {t t'}, step t t' → readout p t = none → readout p t' = none) ∧
        (FiniteResolutionArithmeticEligible Fold address Adm Vis p ω →
          ∀ {t t'}, step t t' →
            (∃ v, typedReadout Adm Vis p (address (Fold ω)) = Readout.value v) ∧
              (address (Fold ω) ∈ Adm p ∧ (Γ p (address (Fold ω))).Nonempty) ∧
              FiniteResolutionArithmeticEligible Fold address Adm Vis p ω' ∧
              (readout p t = none → readout p t' = none)) := by
  classical
  intro hFold
  have hEligibleEquiv :
      FiniteResolutionArithmeticEligible Fold address Adm Vis p ω ↔
        FiniteResolutionArithmeticEligible Fold address Adm Vis p ω' :=
    (paper_recursive_addressing_observer_indexed_finite_resolution_object_eligibility
      Fold address Adm Vis (p := p) (ω := ω) (ω' := ω') hFold).2
  have hNoCreation :
      ∀ {t t'}, step t t' → readout p t = none → readout p t' = none := by
    intro t t' hstep ht
    exact
      paper_recursive_addressing_observer_indexed_value_preserving_no_creation
        readout step hpres hstep ht
  have hNonnull :
      (((∃ v, typedReadout Adm Vis p (address (Fold ω)) = Readout.value v) ↔
          (address (Fold ω) ∈ Adm p ∧ (Γ p (address (Fold ω))).Nonempty)) ∧
        ((address (Fold ω) ∉ Adm p ∨ Γ p (address (Fold ω)) = ∅) →
          ¬ ∃ v, typedReadout Adm Vis p (address (Fold ω)) = Readout.value v)) :=
    paper_recursive_addressing_observer_indexed_nonnull_criterion
      Adm Vis Γ hΓ (p := p) (r := address (Fold ω))
  refine ⟨hEligibleEquiv, hNoCreation, ?_⟩
  intro hEligible t t' hstep
  have hObjectified : address (Fold ω) ∈ Adm p ∧ (Γ p (address (Fold ω))).Nonempty :=
    hNonnull.1.mp hEligible
  exact ⟨hEligible, hObjectified, hEligibleEquiv.mp hEligible, hNoCreation hstep⟩

end Omega.RecursiveAddressing

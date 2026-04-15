import Omega.RecursiveAddressing.ObserverIndexedCommonRefinementDecidability
import Omega.RecursiveAddressing.ObserverIndexedNoRetraction
import Omega.RecursiveAddressing.ObserverIndexedValuePreservingNoCreation

namespace Omega.RecursiveAddressing

set_option maxHeartbeats 400000 in
/-- Paper-facing delayed-classification wrapper: an observer-indexed update can refine which
    previously indexed proposition is now decidable, but it cannot retrocausally create an
    object-level value from a source that was still undefined before the update.
    prop:observer-indexed-delayed-classification-not-retrocausal -/
theorem paper_recursive_addressing_observer_indexed_delayed_classification_not_retrocausal
    {Expr State Value : Type}
    (readout : State → Expr → Option Value)
    (step : Expr → Expr → Prop)
    (hpres : ∀ {p t t' v}, step t t' → readout p t' = some v → readout p t = some v)
    {p : State} {t t' : Expr}
    (hstep : step t t') :
    readout p t = none → readout p t' = none := by
  intro ht
  exact
    paper_recursive_addressing_observer_indexed_value_preserving_no_creation
      readout step hpres hstep ht

set_option maxHeartbeats 400000 in
/-- Paper-facing corollary: observer-indexed updates decide already-indexed facts rather than
    creating a new object-level value ex nihilo.
    cor:observer-indexed-update-decides-not-create -/
theorem paper_recursive_addressing_observer_indexed_update_decides_not_create
    {Expr State Value : Type}
    (readout : State → Expr → Option Value)
    (step : Expr → Expr → Prop)
    (hpres : ∀ {p t t' v}, step t t' → readout p t' = some v → readout p t = some v)
    {p : State} {t t' : Expr}
    (hstep : step t t')
    (ht : readout p t = none) :
    readout p t' = none := by
  exact
    paper_recursive_addressing_observer_indexed_delayed_classification_not_retrocausal
      readout step hpres hstep ht

end Omega.RecursiveAddressing

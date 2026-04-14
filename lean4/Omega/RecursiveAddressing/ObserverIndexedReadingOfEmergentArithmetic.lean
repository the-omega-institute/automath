import Omega.RecursiveAddressing.ObserverIndexedFiniteResolutionObjectEligibility
import Omega.RecursiveAddressing.ObserverIndexedValuePreservingNoCreation

namespace Omega.RecursiveAddressing

/-- Paper-facing wrapper for reading emergent arithmetic through the observer-indexed forcing
interface: fold-equivalent microstates have the same arithmetic eligibility, and value-preserving
rewrites cannot create a value from an undefined source.
    cor:observer-indexed-reading-of-emergent-arithmetic -/
theorem paper_recursive_addressing_observer_indexed_reading_of_emergent_arithmetic
    {Micro State Object Ref Value Expr : Type} [DecidableEq Value]
    (Fold : Micro → Object)
    (address : Object → Ref)
    (Adm : State → Set Ref)
    (Vis : State → Ref → Set Value)
    (readout : State → Expr → Option Value)
    (step : Expr → Expr → Prop)
    (hpres : ∀ {p t t' v}, step t t' → readout p t' = some v → readout p t = some v)
    {p : State} {omega omega' : Micro} :
    Fold omega = Fold omega' →
      (FiniteResolutionArithmeticEligible Fold address Adm Vis p omega ↔
          FiniteResolutionArithmeticEligible Fold address Adm Vis p omega') ∧
        (∀ {t t'}, step t t' → readout p t = none → readout p t' = none) := by
  intro hFold
  constructor
  · exact
      (paper_recursive_addressing_observer_indexed_finite_resolution_object_eligibility
        Fold address Adm Vis (p := p) (ω := omega) (ω' := omega') hFold).2
  · intro t t' hstep ht
    exact
      paper_recursive_addressing_observer_indexed_value_preserving_no_creation
        readout step hpres hstep ht

end Omega.RecursiveAddressing

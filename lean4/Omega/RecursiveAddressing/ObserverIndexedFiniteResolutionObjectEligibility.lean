import Omega.RecursiveAddressing.ObserverIndexedReadoutForcingCriterion

namespace Omega.RecursiveAddressing

open FocusedNonNullReadoutCriterion

/-- A finite-resolution microstate becomes arithmetic-eligible only through the address attached to
its folded object class and a non-`NULL` typed readout at that address. -/
def FiniteResolutionArithmeticEligible
    {Micro State Object Ref Value : Type} [DecidableEq Value]
    (Fold : Micro → Object)
    (address : Object → Ref)
    (Adm : State → Set Ref)
    (Vis : State → Ref → Set Value)
    (p : State) (ω : Micro) : Prop :=
  ∃ v, typedReadout Adm Vis p (address (Fold ω)) = Readout.value v

set_option maxHeartbeats 400000 in
/-- Paper-facing wrapper: fold-equivalent realizations only enter the finite-resolution arithmetic
layer after address formation, protocol admissibility, and a singleton non-`NULL` typed readout.
Hence arithmetic eligibility depends on the folded readout class rather than on the raw
microstate.
    prop:observer-indexed-finite-resolution-object-eligibility -/
theorem paper_recursive_addressing_observer_indexed_finite_resolution_object_eligibility
    {Micro State Object Ref Value : Type} [DecidableEq Value]
    (Fold : Micro → Object)
    (address : Object → Ref)
    (Adm : State → Set Ref)
    (Vis : State → Ref → Set Value)
    {p : State} {ω ω' : Micro}
    (hFold : Fold ω = Fold ω') :
    (FiniteResolutionArithmeticEligible Fold address Adm Vis p ω ↔
        (address (Fold ω) ∈ Adm p ∧ ∃ v, Vis p (address (Fold ω)) = {v})) ∧
      (FiniteResolutionArithmeticEligible Fold address Adm Vis p ω ↔
        FiniteResolutionArithmeticEligible Fold address Adm Vis p ω') := by
  classical
  have hCriterion :
      FiniteResolutionArithmeticEligible Fold address Adm Vis p ω ↔
        (address (Fold ω) ∈ Adm p ∧ ∃ v, Vis p (address (Fold ω)) = {v}) := by
    simpa [FiniteResolutionArithmeticEligible] using
      (paper_recursive_addressing_observer_indexed_readout_forcing_criterion
        Adm Vis
        (fun q p => q = p)
        (by
          intro p q r hEq hr
          simpa [hEq] using hr)
        (by
          intro p q r hEq hr
          simpa [hEq] using rfl)
        (p := p) (q := p) (r := address (Fold ω)) rfl).1
  refine ⟨hCriterion, ?_⟩
  simpa [FiniteResolutionArithmeticEligible, hFold]

end Omega.RecursiveAddressing

import Omega.RecursiveAddressing.ObserverIndexedReadoutForcingCriterion

namespace Omega.RecursiveAddressing

open FocusedNonNullReadoutCriterion

set_option maxHeartbeats 400000 in
/-- Paper-facing common-refinement wrapper: any observer-indexed value already forced at either
parent state persists to the common refinement, and a singleton visible fiber at the common
refinement yields a decided non-null readout there.
    prop:observer-indexed-common-refinement-decidability -/
theorem paper_recursive_addressing_observer_indexed_common_refinement_decidability
    {State Ref Value : Type} [DecidableEq Value]
    (Adm : State → Set Ref) (Vis : State → Ref → Set Value)
    (Refines : State → State → Prop)
    (hAdm : ∀ {p q : State} {r : Ref}, Refines q p → r ∈ Adm p → r ∈ Adm q)
    (hVis : ∀ {p q : State} {r : Ref}, Refines q p → r ∈ Adm p → Vis q r = Vis p r)
    {pu pv puv : State} {r : Ref}
    (hleft : Refines puv pu) (hright : Refines puv pv) :
    (((∃ v, typedReadout Adm Vis pu r = Readout.value v) →
        ∃ v, typedReadout Adm Vis puv r = Readout.value v) ∧
      ((∃ v, typedReadout Adm Vis pv r = Readout.value v) →
        ∃ v, typedReadout Adm Vis puv r = Readout.value v) ∧
      ((r ∈ Adm puv ∧ ∃ v, Vis puv r = {v}) →
        ∃ v, typedReadout Adm Vis puv r = Readout.value v)) := by
  classical
  constructor
  · rintro ⟨v, hread⟩
    exact ⟨v, paper_information_state_typed_readout_persistence_seeds
      Adm Vis Refines hAdm hVis hleft hread⟩
  constructor
  · rintro ⟨v, hread⟩
    exact ⟨v, paper_information_state_typed_readout_persistence_seeds
      Adm Vis Refines hAdm hVis hright hread⟩
  · rintro ⟨hAdmUV, hSingletonUV⟩
    rcases hSingletonUV with ⟨v, hVisUV⟩
    exact ⟨v, paper_information_state_nonnull_readout_criterion_seeds
      Adm Vis hAdmUV hVisUV⟩

end Omega.RecursiveAddressing

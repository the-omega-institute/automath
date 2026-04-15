import Omega.RecursiveAddressing.TypedReadoutPersistence

namespace Omega.RecursiveAddressing.GluingFailureTypedReadoutPersistenceAPAL

open Omega.RecursiveAddressing.FocusedNonNullReadoutCriterion

set_option maxHeartbeats 400000 in
/-- Gluing-failure publication wrapper for refinement stability of defined readouts.
    prop:typed-readout-persistence -/
theorem paper_gluing_failure_typed_readout_persistence_apal
    {State Ref Value : Type} [DecidableEq Value]
    (Adm : State → Set Ref) (Vis : State → Ref → Set Value)
    (Refines : State → State → Prop)
    (hAdm : ∀ {p q : State} {r : Ref}, Refines q p → r ∈ Adm p → r ∈ Adm q)
    (hVis : ∀ {p q : State} {r : Ref}, Refines q p → r ∈ Adm p → Vis q r = Vis p r)
    {p q : State} {r : Ref} {v : Value}
    (href : Refines q p)
    (hread : typedReadout Adm Vis p r = Readout.value v) :
    typedReadout Adm Vis q r = Readout.value v :=
  Omega.RecursiveAddressing.paper_information_state_typed_readout_persistence_package
    Adm Vis Refines hAdm hVis href hread

end Omega.RecursiveAddressing.GluingFailureTypedReadoutPersistenceAPAL

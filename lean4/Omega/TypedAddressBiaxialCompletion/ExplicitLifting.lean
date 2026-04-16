import Omega.RecursiveAddressing.ObserverIndexedExplicitLifting

namespace Omega.TypedAddressBiaxialCompletion

open Omega.RecursiveAddressing.FocusedNonNullReadoutCriterion

set_option maxHeartbeats 400000 in
/-- Paper-facing chapter-local restatement of the observer-indexed explicit lifting theorem:
any axiswise singleton typed readouts on an axis-complete orthogonal family can be transported to
a common lifted state provided the family admits a fusion witness and typed readouts persist along
refinement.
    cor:typed-address-biaxial-completion-explicit-lifting -/
theorem paper_typed_address_biaxial_completion_explicit_lifting
    {Axis State Ref Value : Type} [DecidableEq Axis] [DecidableEq Value]
    (Adm : State → Set Ref) (Vis : State → Ref → Set Value)
    (Refines : State → State → Prop)
    (AxisComplete Orthogonal : State → Finset Axis → (Axis → State) → Prop)
    (hFusion : ∀ {p : State} {K : Finset Axis} {q : Axis → State},
      AxisComplete p K q → Orthogonal p K q → ∃ u, ∀ j, j ∈ K → Refines u (q j))
    (hAdm : ∀ {p q : State} {r : Ref}, Refines q p → r ∈ Adm p → r ∈ Adm q)
    (hVis : ∀ {p q : State} {r : Ref}, Refines q p → r ∈ Adm p → Vis q r = Vis p r)
    {p : State} {K : Finset Axis} {q : Axis → State} {r : Axis → Ref} {v : Axis → Value}
    (hcomplete : AxisComplete p K q)
    (horth : Orthogonal p K q)
    (hread : ∀ j, j ∈ K → typedReadout Adm Vis (q j) (r j) = Readout.value (v j)) :
    ∃ u, ∀ j, j ∈ K → typedReadout Adm Vis u (r j) = Readout.value (v j) := by
  exact Omega.RecursiveAddressing.paper_recursive_addressing_observer_indexed_explicit_lifting
    Adm Vis Refines AxisComplete Orthogonal hFusion hAdm hVis hcomplete horth hread

end Omega.TypedAddressBiaxialCompletion

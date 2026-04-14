import Omega.RecursiveAddressing.TypedReadoutPersistence

namespace Omega.RecursiveAddressing

open FocusedNonNullReadoutCriterion

set_option maxHeartbeats 400000 in
/-- Paper-facing observer-indexed explicit lifting: if an axis-complete orthogonal family can be
fused to a common refinement, then singleton typed readouts forced on each axis persist to that
fusion state.
    cor:observer-indexed-explicit-lifting -/
theorem paper_recursive_addressing_observer_indexed_explicit_lifting
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
  rcases hFusion hcomplete horth with ⟨u, hu⟩
  refine ⟨u, ?_⟩
  intro j hj
  exact paper_information_state_typed_readout_persistence_package
    Adm Vis Refines hAdm hVis (hu j hj) (hread j hj)

end Omega.RecursiveAddressing

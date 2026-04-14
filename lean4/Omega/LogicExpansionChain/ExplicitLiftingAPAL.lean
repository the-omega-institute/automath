import Mathlib.Data.Finset.Basic

namespace Omega.LogicExpansionChain.ExplicitLiftingAPAL

set_option maxHeartbeats 400000 in
/-- APAL publication wrapper for the explicit lifting principle.
    cor:explicit-lifting -/
theorem paper_conservative_extension_explicit_lifting_apal
    {Axis State Ref Value : Type} [DecidableEq Axis]
    (Refines : State → State → Prop)
    (ReadAt : State → Ref → Value → Prop)
    (AxisComplete Orthogonal : State → Finset Axis → (Axis → State) → Prop)
    (hFusion : ∀ {p : State} {K : Finset Axis} {q : Axis → State},
      AxisComplete p K q → Orthogonal p K q → ∃ u, ∀ j, j ∈ K → Refines u (q j))
    (hPersist : ∀ {q u : State} {r : Ref} {v : Value},
      Refines u q → ReadAt q r v → ReadAt u r v)
    {p : State} {K : Finset Axis} {q : Axis → State} {r : Axis → Ref} {v : Axis → Value}
    (hcomplete : AxisComplete p K q)
    (horth : Orthogonal p K q)
    (hread : ∀ j, j ∈ K → ReadAt (q j) (r j) (v j)) :
    ∃ u, ∀ j, j ∈ K → ReadAt u (r j) (v j) := by
  rcases hFusion hcomplete horth with ⟨u, hu⟩
  refine ⟨u, ?_⟩
  intro j hj
  exact hPersist (hu j hj) (hread j hj)

end Omega.LogicExpansionChain.ExplicitLiftingAPAL

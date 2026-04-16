import Mathlib.Data.Finset.Basic

namespace Omega.LogicExpansionChain

/-- Paper-facing witness extraction: axis completeness for an orthogonal family already packages a
jointly reachable fusion state.
    prop:logic-expansion-orthogonal-family-joint-reachability -/
theorem paper_logic_expansion_orthogonal_family_joint_reachability
    {Axis State : Type} [DecidableEq Axis]
    (ReachK : State → Finset Axis → State → Prop)
    (Equiv : Axis → State → State → Prop)
    (AxisComplete Orthogonal : State → Finset Axis → (Axis → State) → Prop)
    (hcomplete : ∀ {p : State} {K : Finset Axis} {q : Axis → State},
      AxisComplete p K q → Orthogonal p K q →
        ∃ s, ReachK p K s ∧ ∀ j, j ∈ K → Equiv j s (q j))
    {p : State} {K : Finset Axis} {q : Axis → State}
    (haxes : AxisComplete p K q)
    (horth : Orthogonal p K q) :
    ∃ s, ReachK p K s ∧ ∀ j, j ∈ K → Equiv j s (q j) := by
  exact hcomplete haxes horth

end Omega.LogicExpansionChain

import Omega.LogicExpansionChain.StateTheoryMonotonicity

namespace Omega.LogicExpansionChain

set_option maxHeartbeats 400000 in
/-- Publication-facing seed for monotone growth of state theories in the focused APAL paper.
    cor:state-theory-monotonicity -/
theorem paper_information_state_state_theory_monotonicity_focused_seeds
    {Context Val Formula : Type} (satisfies : Val → Formula → Prop)
    (p q : ForcingPersistence.InformationState Context Val)
    (href : q.realizations ⊆ p.realizations) :
    stateTheory satisfies p ⊆ stateTheory satisfies q :=
  paper_information_state_theory_monotonicity_seeds satisfies p q href

end Omega.LogicExpansionChain

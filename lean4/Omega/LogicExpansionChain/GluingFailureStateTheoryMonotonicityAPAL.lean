import Omega.LogicExpansionChain.StateTheoryMonotonicity

namespace Omega.LogicExpansionChain

open ForcingPersistence

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for monotone growth of state theories in the gluing-failure APAL
paper.
    cor:state-theory-monotonicity -/
theorem paper_gluing_failure_state_theory_monotonicity_apal
    {Context Val Formula : Type} (satisfies : Val → Formula → Prop)
    (p q : InformationState Context Val)
    (href : q.realizations ⊆ p.realizations) :
    stateTheory satisfies p ⊆ stateTheory satisfies q :=
  paper_information_state_theory_monotonicity_seeds satisfies p q href

end Omega.LogicExpansionChain

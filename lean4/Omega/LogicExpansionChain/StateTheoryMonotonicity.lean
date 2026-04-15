import Omega.LogicExpansionChain.ForcingPersistence

namespace Omega.LogicExpansionChain

open ForcingPersistence

/-- The collection of formulas forced at a state. -/
def stateTheory {Context Val Formula : Type}
    (satisfies : Val → Formula → Prop) (p : InformationState Context Val) : Set Formula :=
  {φ | Forces satisfies p φ}

set_option maxHeartbeats 400000 in
/-- Paper-facing seed: refining a state can only enlarge its forced theory.
    cor:state-theory-monotonicity -/
theorem paper_information_state_theory_monotonicity_seeds
    {Context Val Formula : Type} (satisfies : Val → Formula → Prop)
    (p q : InformationState Context Val)
    (href : q.realizations ⊆ p.realizations) :
    stateTheory satisfies p ⊆ stateTheory satisfies q := by
  intro φ hφ
  simpa [stateTheory] using fun ρ hρ => (show Forces satisfies p φ from hφ) ρ (href hρ)

end Omega.LogicExpansionChain

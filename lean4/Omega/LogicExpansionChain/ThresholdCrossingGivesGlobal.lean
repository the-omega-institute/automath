import Omega.LogicExpansionChain.LocalToGlobal

namespace Omega.LogicExpansionChain

set_option maxHeartbeats 400000 in
/-- Threshold-crossing is just the local-to-global gluing hypothesis under the paper's name.
    prop:logic-expansion-threshold-crossing-gives-global -/
theorem paper_logic_expansion_threshold_crossing_gives_global
    {State Ref Obj Section : Type*}
    (address : State → Ref → Obj) (F : Obj → Set Section)
    (crossesThreshold :
      ∀ W : Omega.LogicExpansionChain.CompatibleLocalFamily Obj Section,
        W.compatible →
        (∀ i, W.localSec i ∈ F (W.cover i)) →
        ∃ σ, σ ∈ F W.target)
    {p : State} {r : Ref}
    (hComp : Omega.LogicExpansionChain.CompSec address F p r) :
    Omega.LogicExpansionChain.Sec address F p r := by
  exact paper_logic_expansion_local_to_global address F crossesThreshold hComp

end Omega.LogicExpansionChain

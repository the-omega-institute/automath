import Omega.LogicExpansionChain.LocalToGlobal

namespace Omega.LogicExpansionChain

set_option maxHeartbeats 400000 in
/-- Crossing the gluing-closure threshold is exactly the hypothesis needed to turn a compatible
    local family into a global section at `address p r`.
    prop:logic-expansion-threshold-crossing-gives-global -/
theorem paper_logic_expansion_threshold_crossing_gives_global
    {State Ref Obj Section : Type*}
    (address : State → Ref → Obj) (F : Obj → Set Section)
    {p : State} {r : Ref}
    (hThreshold :
      ∀ W : CompatibleLocalFamily Obj Section,
        W.target = address p r →
        W.compatible →
        (∀ i, W.localSec i ∈ F (W.cover i)) →
        ∃ σ, σ ∈ F W.target)
    (hComp : CompSec address F p r) :
    Sec address F p r := by
  rcases hComp with ⟨W, htarget, hWcompat, hWlocal⟩
  rcases hThreshold W htarget hWcompat hWlocal with ⟨σ, hσ⟩
  exact ⟨σ, by simpa [Sec, htarget] using hσ⟩

end Omega.LogicExpansionChain

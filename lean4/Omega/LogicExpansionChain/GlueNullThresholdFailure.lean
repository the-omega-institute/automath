import Omega.LogicExpansionChain.ThresholdCrossingGivesGlobal

namespace Omega.LogicExpansionChain

set_option maxHeartbeats 400000 in
/-- Glue-null means compatibility without a global section, so any threshold-crossing principle
    would immediately contradict the failure of `Sec`.
    cor:logic-expansion-glue-null-threshold-failure -/
theorem paper_logic_expansion_glue_null_threshold_failure
    {State Ref Obj Section : Type*}
    (address : State → Ref → Obj) (F : Obj → Set Section)
    {p : State} {r : Ref}
    (hNullGlue : CompSec address F p r ∧ ¬ Sec address F p r) :
    ¬ (∀ W : CompatibleLocalFamily Obj Section,
        W.target = address p r →
        W.compatible →
        (∀ i, W.localSec i ∈ F (W.cover i)) →
        ∃ σ, σ ∈ F W.target) := by
  intro hThreshold
  exact hNullGlue.2
    (paper_logic_expansion_threshold_crossing_gives_global address F hThreshold hNullGlue.1)

end Omega.LogicExpansionChain

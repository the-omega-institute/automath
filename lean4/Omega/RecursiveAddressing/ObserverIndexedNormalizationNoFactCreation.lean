import Omega.LogicExpansionChain.NormalizationNoFactCreation

namespace Omega.RecursiveAddressing

set_option maxHeartbeats 400000 in
/-- Paper-facing seed: object-level normalization in the observer-indexed readout layer only
    changes representation and cannot create a new value from an undefined term.
    cor:observer-indexed-normalization-no-fact-creation -/
theorem paper_recursive_addressing_observer_indexed_normalization_no_fact_creation_seeds
    {Expr State Value : Type}
    (readout : State → Expr → Option Value) (p : State)
    {n : Nat} (E : Nat → Expr)
    (hstep : ∀ i, i < n → ∀ v, readout p (E (i + 1)) = some v → readout p (E i) = some v)
    {v : Value}
    (hend : readout p (E n) = some v) :
    readout p (E 0) = some v :=
  Omega.LogicExpansionChain.paper_conservative_extension_normalization_no_fact_creation_seeds
    readout p E hstep hend

end Omega.RecursiveAddressing
